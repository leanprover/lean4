// Lean compiler output
// Module: Lean.Meta.Sym.AbstractS
// Imports: public import Lean.Meta.Sym.SymM import Lean.Meta.Sym.ReplaceS import Init.Omega
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
lean_object* l_Lean_LocalDecl_index(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_instInhabitedLocalDecl_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_share1___redArg(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Builder_assertShared(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3;
static const lean_closure_object l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__11(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__0_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__4_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__5 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__5_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__6 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "_private.Lean.Meta.Sym.ReplaceS.0.Lean.Meta.Sym.visit"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Sym.ReplaceS"};
static const lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_4_ = ((lean_object*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__2));
v___x_5_ = lean_unsigned_to_nat(14u);
v___x_6_ = lean_unsigned_to_nat(22u);
v___x_7_ = ((lean_object*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__1));
v___x_8_ = ((lean_object*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__0));
v___x_9_ = l_mkPanicMessageWithDecl(v___x_8_, v___x_7_, v___x_6_, v___x_5_, v___x_4_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(lean_object* v_toDeBruijn_x3f_12_, lean_object* v___x_13_, lean_object* v_maxFVar_14_, lean_object* v_minIndex_15_, lean_object* v_lctx_16_, lean_object* v___x_17_, lean_object* v_e_18_, lean_object* v_offset_19_, uint8_t v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v___y_23_; lean_object* v___y_31_; 
switch(lean_obj_tag(v_e_18_))
{
case 1:
{
lean_object* v_fvarId_36_; lean_object* v___x_37_; 
lean_dec_ref(v_lctx_16_);
v_fvarId_36_ = lean_ctor_get(v_e_18_, 0);
lean_inc(v_fvarId_36_);
v___x_37_ = lean_apply_1(v_toDeBruijn_x3f_12_, v_fvarId_36_);
if (lean_obj_tag(v___x_37_) == 1)
{
lean_object* v_val_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_58_; 
lean_dec_ref_known(v_e_18_, 1);
v_val_38_ = lean_ctor_get(v___x_37_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v___x_37_);
if (v_isSharedCheck_58_ == 0)
{
v___x_40_ = v___x_37_;
v_isShared_41_ = v_isSharedCheck_58_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_val_38_);
lean_dec(v___x_37_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_58_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_42_; lean_object* v___x_2873__overap_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v_fst_46_; lean_object* v_snd_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_57_; 
v___x_42_ = lean_nat_add(v_offset_19_, v_val_38_);
lean_dec(v_val_38_);
v___x_2873__overap_43_ = l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v___x_13_, v___x_42_);
v___x_44_ = lean_box(v___y_20_);
v___x_45_ = lean_apply_2(v___x_2873__overap_43_, v___x_44_, v___y_21_);
v_fst_46_ = lean_ctor_get(v___x_45_, 0);
v_snd_47_ = lean_ctor_get(v___x_45_, 1);
v_isSharedCheck_57_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_57_ == 0)
{
v___x_49_ = v___x_45_;
v_isShared_50_ = v_isSharedCheck_57_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_snd_47_);
lean_inc(v_fst_46_);
lean_dec(v___x_45_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_57_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_52_; 
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 0, v_fst_46_);
v___x_52_ = v___x_40_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_fst_46_);
v___x_52_ = v_reuseFailAlloc_56_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
lean_object* v___x_54_; 
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 0, v___x_52_);
v___x_54_ = v___x_49_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_52_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v_snd_47_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
}
else
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v___x_37_);
lean_dec_ref(v___x_13_);
v___x_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_59_, 0, v_e_18_);
v___x_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v___y_21_);
return v___x_60_;
}
}
case 9:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
lean_dec_ref(v_lctx_16_);
lean_dec_ref(v___x_13_);
lean_dec_ref(v_toDeBruijn_x3f_12_);
v___x_61_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_61_, 0, v_e_18_);
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___y_21_);
return v___x_62_;
}
case 2:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
lean_dec_ref(v_lctx_16_);
lean_dec_ref(v___x_13_);
lean_dec_ref(v_toDeBruijn_x3f_12_);
v___x_63_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_63_, 0, v_e_18_);
v___x_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___y_21_);
return v___x_64_;
}
case 0:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec_ref(v_lctx_16_);
lean_dec_ref(v___x_13_);
lean_dec_ref(v_toDeBruijn_x3f_12_);
v___x_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_65_, 0, v_e_18_);
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___y_21_);
return v___x_66_;
}
case 4:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec_ref(v_lctx_16_);
lean_dec_ref(v___x_13_);
lean_dec_ref(v_toDeBruijn_x3f_12_);
v___x_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_67_, 0, v_e_18_);
v___x_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v___y_21_);
return v___x_68_;
}
case 3:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec_ref(v_lctx_16_);
lean_dec_ref(v___x_13_);
lean_dec_ref(v_toDeBruijn_x3f_12_);
v___x_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_69_, 0, v_e_18_);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v___y_21_);
return v___x_70_;
}
default: 
{
uint8_t v___x_71_; 
lean_dec_ref(v___x_13_);
lean_dec_ref(v_toDeBruijn_x3f_12_);
v___x_71_ = l_Lean_Expr_hasFVar(v_e_18_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec_ref(v_lctx_16_);
v___x_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_72_, 0, v_e_18_);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___y_21_);
return v___x_73_;
}
else
{
lean_object* v___f_74_; lean_object* v___f_75_; lean_object* v___x_76_; 
v___f_74_ = ((lean_object*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4));
v___f_75_ = ((lean_object*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__5));
lean_inc_ref(v_e_18_);
v___x_76_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_74_, v___f_75_, v_maxFVar_14_, v_e_18_);
if (lean_obj_tag(v___x_76_) == 1)
{
lean_object* v_val_77_; 
v_val_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_val_77_);
lean_dec_ref_known(v___x_76_, 1);
if (lean_obj_tag(v_val_77_) == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = lean_box(0);
v___x_79_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_80_ = l_panic___redArg(v___x_78_, v___x_79_);
v___y_31_ = v___x_80_;
goto v___jp_30_;
}
else
{
lean_object* v_val_81_; 
v_val_81_ = lean_ctor_get(v_val_77_, 0);
lean_inc(v_val_81_);
lean_dec_ref_known(v_val_77_, 1);
v___y_31_ = v_val_81_;
goto v___jp_30_;
}
}
else
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v___x_76_);
lean_dec_ref(v_e_18_);
lean_dec_ref(v_lctx_16_);
v___x_82_ = lean_box(0);
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___y_21_);
return v___x_83_;
}
}
}
}
v___jp_22_:
{
lean_object* v_maxIndex_24_; uint8_t v___x_25_; 
v_maxIndex_24_ = l_Lean_LocalDecl_index(v___y_23_);
lean_dec_ref(v___y_23_);
v___x_25_ = lean_nat_dec_lt(v_maxIndex_24_, v_minIndex_15_);
lean_dec(v_maxIndex_24_);
if (v___x_25_ == 0)
{
lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec_ref(v_e_18_);
v___x_26_ = lean_box(0);
v___x_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
lean_ctor_set(v___x_27_, 1, v___y_21_);
return v___x_27_;
}
else
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_28_, 0, v_e_18_);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___y_21_);
return v___x_29_;
}
}
v___jp_30_:
{
lean_object* v___x_32_; 
v___x_32_ = lean_local_ctx_find(v_lctx_16_, v___y_31_);
if (lean_obj_tag(v___x_32_) == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_34_ = l_panic___redArg(v___x_17_, v___x_33_);
v___y_23_ = v___x_34_;
goto v___jp_22_;
}
else
{
lean_object* v_val_35_; 
v_val_35_ = lean_ctor_get(v___x_32_, 0);
lean_inc(v_val_35_);
lean_dec_ref_known(v___x_32_, 1);
v___y_23_ = v_val_35_;
goto v___jp_22_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___boxed(lean_object* v_toDeBruijn_x3f_84_, lean_object* v___x_85_, lean_object* v_maxFVar_86_, lean_object* v_minIndex_87_, lean_object* v_lctx_88_, lean_object* v___x_89_, lean_object* v_e_90_, lean_object* v_offset_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
uint8_t v___y_2965__boxed_94_; lean_object* v_res_95_; 
v___y_2965__boxed_94_ = lean_unbox(v___y_92_);
v_res_95_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(v_toDeBruijn_x3f_84_, v___x_85_, v_maxFVar_86_, v_minIndex_87_, v_lctx_88_, v___x_89_, v_e_90_, v_offset_91_, v___y_2965__boxed_94_, v___y_93_);
lean_dec(v_offset_91_);
lean_dec_ref(v___x_89_);
lean_dec(v_minIndex_87_);
lean_dec_ref(v_maxFVar_86_);
return v_res_95_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_box(0);
v___x_97_ = lean_unsigned_to_nat(16u);
v___x_98_ = lean_mk_array(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0);
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore(lean_object* v_e_102_, lean_object* v_lctx_103_, lean_object* v_maxFVar_104_, lean_object* v_minFVarId_105_, lean_object* v_toDeBruijn_x3f_106_, uint8_t v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___y_112_; lean_object* v___x_196_; 
v___x_109_ = l_Lean_instInhabitedLocalDecl_default;
v___x_110_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
lean_inc_ref(v_lctx_103_);
v___x_196_ = lean_local_ctx_find(v_lctx_103_, v_minFVarId_105_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_198_ = l_panic___redArg(v___x_109_, v___x_197_);
v___y_112_ = v___x_198_;
goto v___jp_111_;
}
else
{
lean_object* v_val_199_; 
v_val_199_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_val_199_);
lean_dec_ref_known(v___x_196_, 1);
v___y_112_ = v_val_199_;
goto v___jp_111_;
}
v___jp_111_:
{
lean_object* v_minIndex_113_; lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v_fst_117_; 
v_minIndex_113_ = l_Lean_LocalDecl_index(v___y_112_);
lean_dec_ref(v___y_112_);
lean_inc_ref(v_lctx_103_);
lean_inc(v_minIndex_113_);
lean_inc_ref(v_maxFVar_104_);
lean_inc_ref(v_toDeBruijn_x3f_106_);
v___f_114_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___boxed), 10, 6);
lean_closure_set(v___f_114_, 0, v_toDeBruijn_x3f_106_);
lean_closure_set(v___f_114_, 1, v___x_110_);
lean_closure_set(v___f_114_, 2, v_maxFVar_104_);
lean_closure_set(v___f_114_, 3, v_minIndex_113_);
lean_closure_set(v___f_114_, 4, v_lctx_103_);
lean_closure_set(v___f_114_, 5, v___x_109_);
v___x_115_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_e_102_);
v___x_116_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(v_toDeBruijn_x3f_106_, v___x_110_, v_maxFVar_104_, v_minIndex_113_, v_lctx_103_, v___x_109_, v_e_102_, v___x_115_, v_a_107_, v_a_108_);
lean_dec(v_minIndex_113_);
lean_dec_ref(v_maxFVar_104_);
v_fst_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_fst_117_);
if (lean_obj_tag(v_fst_117_) == 1)
{
lean_object* v_snd_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_126_; 
lean_dec_ref(v___f_114_);
lean_dec_ref(v_e_102_);
v_snd_118_ = lean_ctor_get(v___x_116_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_126_ == 0)
{
lean_object* v_unused_127_; 
v_unused_127_ = lean_ctor_get(v___x_116_, 0);
lean_dec(v_unused_127_);
v___x_120_ = v___x_116_;
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_snd_118_);
lean_dec(v___x_116_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v_val_122_; lean_object* v___x_124_; 
v_val_122_ = lean_ctor_get(v_fst_117_, 0);
lean_inc(v_val_122_);
lean_dec_ref_known(v_fst_117_, 1);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v_val_122_);
v___x_124_ = v___x_120_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_val_122_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_snd_118_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
else
{
lean_dec(v_fst_117_);
switch(lean_obj_tag(v_e_102_))
{
case 9:
{
lean_object* v_snd_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_135_; 
lean_dec_ref(v___f_114_);
v_snd_128_ = lean_ctor_get(v___x_116_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_135_ == 0)
{
lean_object* v_unused_136_; 
v_unused_136_ = lean_ctor_get(v___x_116_, 0);
lean_dec(v_unused_136_);
v___x_130_ = v___x_116_;
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_snd_128_);
lean_dec(v___x_116_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 0, v_e_102_);
v___x_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_e_102_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_snd_128_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
case 2:
{
lean_object* v_snd_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
lean_dec_ref(v___f_114_);
v_snd_137_ = lean_ctor_get(v___x_116_, 1);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_144_ == 0)
{
lean_object* v_unused_145_; 
v_unused_145_ = lean_ctor_get(v___x_116_, 0);
lean_dec(v_unused_145_);
v___x_139_ = v___x_116_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_snd_137_);
lean_dec(v___x_116_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 0, v_e_102_);
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_e_102_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_snd_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
case 0:
{
lean_object* v_snd_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec_ref(v___f_114_);
v_snd_146_ = lean_ctor_get(v___x_116_, 1);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_153_ == 0)
{
lean_object* v_unused_154_; 
v_unused_154_ = lean_ctor_get(v___x_116_, 0);
lean_dec(v_unused_154_);
v___x_148_ = v___x_116_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_snd_146_);
lean_dec(v___x_116_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v_e_102_);
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_e_102_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_snd_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
case 1:
{
lean_object* v_snd_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
lean_dec_ref(v___f_114_);
v_snd_155_ = lean_ctor_get(v___x_116_, 1);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_162_ == 0)
{
lean_object* v_unused_163_; 
v_unused_163_ = lean_ctor_get(v___x_116_, 0);
lean_dec(v_unused_163_);
v___x_157_ = v___x_116_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_snd_155_);
lean_dec(v___x_116_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v_e_102_);
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_e_102_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_snd_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
case 4:
{
lean_object* v_snd_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
lean_dec_ref(v___f_114_);
v_snd_164_ = lean_ctor_get(v___x_116_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_171_ == 0)
{
lean_object* v_unused_172_; 
v_unused_172_ = lean_ctor_get(v___x_116_, 0);
lean_dec(v_unused_172_);
v___x_166_ = v___x_116_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_snd_164_);
lean_dec(v___x_116_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v_e_102_);
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_e_102_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_snd_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
case 3:
{
lean_object* v_snd_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
lean_dec_ref(v___f_114_);
v_snd_173_ = lean_ctor_get(v___x_116_, 1);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_180_ == 0)
{
lean_object* v_unused_181_; 
v_unused_181_ = lean_ctor_get(v___x_116_, 0);
lean_dec(v_unused_181_);
v___x_175_ = v___x_116_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_snd_173_);
lean_dec(v___x_116_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v_e_102_);
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_e_102_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_snd_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
default: 
{
lean_object* v_snd_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v_fst_185_; lean_object* v_snd_186_; lean_object* v_fst_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
v_snd_182_ = lean_ctor_get(v___x_116_, 1);
lean_inc(v_snd_182_);
lean_dec_ref(v___x_116_);
v___x_183_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1);
v___x_184_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(v_e_102_, v___x_115_, v___f_114_, v___x_183_, v_a_107_, v_snd_182_);
v_fst_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_fst_185_);
v_snd_186_ = lean_ctor_get(v___x_184_, 1);
lean_inc(v_snd_186_);
lean_dec_ref(v___x_184_);
v_fst_187_ = lean_ctor_get(v_fst_185_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v_fst_185_);
if (v_isSharedCheck_194_ == 0)
{
lean_object* v_unused_195_; 
v_unused_195_ = lean_ctor_get(v_fst_185_, 1);
lean_dec(v_unused_195_);
v___x_189_ = v_fst_185_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_fst_187_);
lean_dec(v_fst_185_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 1, v_snd_186_);
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_fst_187_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_snd_186_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___boxed(lean_object* v_e_200_, lean_object* v_lctx_201_, lean_object* v_maxFVar_202_, lean_object* v_minFVarId_203_, lean_object* v_toDeBruijn_x3f_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
uint8_t v_a_boxed_207_; lean_object* v_res_208_; 
v_a_boxed_207_ = lean_unbox(v_a_205_);
v_res_208_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore(v_e_200_, v_lctx_201_, v_maxFVar_202_, v_minFVarId_203_, v_toDeBruijn_x3f_204_, v_a_boxed_207_, v_a_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(lean_object* v_start_209_, lean_object* v_xs_210_, lean_object* v_fvarId_211_, lean_object* v_bidx_212_, lean_object* v_i_213_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_214_ = lean_array_fget_borrowed(v_xs_210_, v_i_213_);
v___x_215_ = l_Lean_Expr_fvarId_x21(v___x_214_);
v___x_216_ = l_Lean_instBEqFVarId_beq(v___x_215_, v_fvarId_211_);
lean_dec(v___x_215_);
if (v___x_216_ == 0)
{
uint8_t v___x_217_; 
v___x_217_ = lean_nat_dec_lt(v_start_209_, v_i_213_);
if (v___x_217_ == 0)
{
lean_object* v___x_218_; 
lean_dec(v_i_213_);
lean_dec(v_bidx_212_);
v___x_218_ = lean_box(0);
return v___x_218_;
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = lean_nat_add(v_bidx_212_, v___x_219_);
lean_dec(v_bidx_212_);
v___x_221_ = lean_nat_sub(v_i_213_, v___x_219_);
lean_dec(v_i_213_);
v_bidx_212_ = v___x_220_;
v_i_213_ = v___x_221_;
goto _start;
}
}
else
{
lean_object* v___x_223_; 
lean_dec(v_i_213_);
v___x_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_223_, 0, v_bidx_212_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg___boxed(lean_object* v_start_224_, lean_object* v_xs_225_, lean_object* v_fvarId_226_, lean_object* v_bidx_227_, lean_object* v_i_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_224_, v_xs_225_, v_fvarId_226_, v_bidx_227_, v_i_228_);
lean_dec(v_fvarId_226_);
lean_dec_ref(v_xs_225_);
lean_dec(v_start_224_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go(lean_object* v_start_230_, lean_object* v_xs_231_, lean_object* v_fvarId_232_, lean_object* v_bidx_233_, lean_object* v_i_234_, lean_object* v_h_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_230_, v_xs_231_, v_fvarId_232_, v_bidx_233_, v_i_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___boxed(lean_object* v_start_237_, lean_object* v_xs_238_, lean_object* v_fvarId_239_, lean_object* v_bidx_240_, lean_object* v_i_241_, lean_object* v_h_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go(v_start_237_, v_xs_238_, v_fvarId_239_, v_bidx_240_, v_i_241_, v_h_242_);
lean_dec(v_fvarId_239_);
lean_dec_ref(v_xs_238_);
lean_dec(v_start_237_);
return v_res_243_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__0(void){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_244_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__1(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__0);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(lean_object* v_00_u03b2_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__1);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(lean_object* v_msg_249_){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = l_Lean_instInhabitedLocalDecl_default;
v___x_251_ = lean_panic_fn_borrowed(v___x_250_, v_msg_249_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(lean_object* v_idx_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = l_Lean_Expr_bvar___override(v_idx_252_);
v___x_255_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_254_, v___y_253_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(lean_object* v_idx_256_, uint8_t v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_idx_256_, v___y_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___boxed(lean_object* v_idx_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
uint8_t v___y_25259__boxed_263_; lean_object* v_res_264_; 
v___y_25259__boxed_263_ = lean_unbox(v___y_261_);
v_res_264_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(v_idx_260_, v___y_25259__boxed_263_, v___y_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(lean_object* v_msg_265_){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_box(0);
v___x_267_ = lean_panic_fn_borrowed(v___x_266_, v_msg_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__12(lean_object* v_structName_268_, lean_object* v_idx_269_, lean_object* v_struct_270_, lean_object* v___y_271_, uint8_t v___y_272_, lean_object* v___y_273_){
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
lean_object* v___x_289_; lean_object* v_snd_290_; 
lean_inc_ref(v_struct_270_);
v___x_289_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_struct_270_, v___y_272_, v___y_273_);
v_snd_290_ = lean_ctor_get(v___x_289_, 1);
lean_inc(v_snd_290_);
lean_dec_ref(v___x_289_);
v___y_275_ = v___y_271_;
v___y_276_ = v_snd_290_;
goto v___jp_274_;
}
v___jp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_fst_279_; lean_object* v_snd_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_288_; 
v___x_277_ = l_Lean_Expr_proj___override(v_structName_268_, v_idx_269_, v_struct_270_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__12___boxed(lean_object* v_structName_291_, lean_object* v_idx_292_, lean_object* v_struct_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
uint8_t v___y_25272__boxed_297_; lean_object* v_res_298_; 
v___y_25272__boxed_297_ = lean_unbox(v___y_295_);
v_res_298_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__12(v_structName_291_, v_idx_292_, v_struct_293_, v___y_294_, v___y_25272__boxed_297_, v___y_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__11(lean_object* v_d_299_, lean_object* v_e_300_, lean_object* v___y_301_, uint8_t v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___y_305_; lean_object* v___y_306_; 
if (v___y_302_ == 0)
{
v___y_305_ = v___y_301_;
v___y_306_ = v___y_303_;
goto v___jp_304_;
}
else
{
lean_object* v___x_319_; lean_object* v_snd_320_; 
lean_inc_ref(v_e_300_);
v___x_319_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_300_, v___y_302_, v___y_303_);
v_snd_320_ = lean_ctor_get(v___x_319_, 1);
lean_inc(v_snd_320_);
lean_dec_ref(v___x_319_);
v___y_305_ = v___y_301_;
v___y_306_ = v_snd_320_;
goto v___jp_304_;
}
v___jp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v_fst_309_; lean_object* v_snd_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_318_; 
v___x_307_ = l_Lean_Expr_mdata___override(v_d_299_, v_e_300_);
v___x_308_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_307_, v___y_306_);
v_fst_309_ = lean_ctor_get(v___x_308_, 0);
v_snd_310_ = lean_ctor_get(v___x_308_, 1);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_318_ == 0)
{
v___x_312_ = v___x_308_;
v_isShared_313_ = v_isSharedCheck_318_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_snd_310_);
lean_inc(v_fst_309_);
lean_dec(v___x_308_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_318_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 1, v___y_305_);
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_fst_309_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v___y_305_);
v___x_315_ = v_reuseFailAlloc_317_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_316_; 
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v_snd_310_);
return v___x_316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__11___boxed(lean_object* v_d_321_, lean_object* v_e_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
uint8_t v___y_25316__boxed_326_; lean_object* v_res_327_; 
v___y_25316__boxed_326_ = lean_unbox(v___y_324_);
v_res_327_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__11(v_d_321_, v_e_322_, v___y_323_, v___y_25316__boxed_326_, v___y_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__9(lean_object* v_x_328_, uint8_t v_bi_329_, lean_object* v_t_330_, lean_object* v_b_331_, lean_object* v___y_332_, uint8_t v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___y_336_; lean_object* v___y_337_; 
if (v___y_333_ == 0)
{
v___y_336_ = v___y_332_;
v___y_337_ = v___y_334_;
goto v___jp_335_;
}
else
{
lean_object* v___x_350_; lean_object* v_snd_351_; lean_object* v___x_352_; lean_object* v_snd_353_; 
lean_inc_ref(v_t_330_);
v___x_350_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_330_, v___y_333_, v___y_334_);
v_snd_351_ = lean_ctor_get(v___x_350_, 1);
lean_inc(v_snd_351_);
lean_dec_ref(v___x_350_);
lean_inc_ref(v_b_331_);
v___x_352_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_331_, v___y_333_, v_snd_351_);
v_snd_353_ = lean_ctor_get(v___x_352_, 1);
lean_inc(v_snd_353_);
lean_dec_ref(v___x_352_);
v___y_336_ = v___y_332_;
v___y_337_ = v_snd_353_;
goto v___jp_335_;
}
v___jp_335_:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v_fst_340_; lean_object* v_snd_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_349_; 
v___x_338_ = l_Lean_Expr_forallE___override(v_x_328_, v_t_330_, v_b_331_, v_bi_329_);
v___x_339_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_338_, v___y_337_);
v_fst_340_ = lean_ctor_get(v___x_339_, 0);
v_snd_341_ = lean_ctor_get(v___x_339_, 1);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_349_ == 0)
{
v___x_343_ = v___x_339_;
v_isShared_344_ = v_isSharedCheck_349_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_snd_341_);
lean_inc(v_fst_340_);
lean_dec(v___x_339_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_349_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 1, v___y_336_);
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_fst_340_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v___y_336_);
v___x_346_ = v_reuseFailAlloc_348_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_347_; 
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v_snd_341_);
return v___x_347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__9___boxed(lean_object* v_x_354_, lean_object* v_bi_355_, lean_object* v_t_356_, lean_object* v_b_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
uint8_t v_bi_boxed_361_; uint8_t v___y_25360__boxed_362_; lean_object* v_res_363_; 
v_bi_boxed_361_ = lean_unbox(v_bi_355_);
v___y_25360__boxed_362_ = lean_unbox(v___y_359_);
v_res_363_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__9(v_x_354_, v_bi_boxed_361_, v_t_356_, v_b_357_, v___y_358_, v___y_25360__boxed_362_, v___y_360_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__8(lean_object* v_x_364_, uint8_t v_bi_365_, lean_object* v_t_366_, lean_object* v_b_367_, lean_object* v___y_368_, uint8_t v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___y_372_; lean_object* v___y_373_; 
if (v___y_369_ == 0)
{
v___y_372_ = v___y_368_;
v___y_373_ = v___y_370_;
goto v___jp_371_;
}
else
{
lean_object* v___x_386_; lean_object* v_snd_387_; lean_object* v___x_388_; lean_object* v_snd_389_; 
lean_inc_ref(v_t_366_);
v___x_386_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_366_, v___y_369_, v___y_370_);
v_snd_387_ = lean_ctor_get(v___x_386_, 1);
lean_inc(v_snd_387_);
lean_dec_ref(v___x_386_);
lean_inc_ref(v_b_367_);
v___x_388_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_367_, v___y_369_, v_snd_387_);
v_snd_389_ = lean_ctor_get(v___x_388_, 1);
lean_inc(v_snd_389_);
lean_dec_ref(v___x_388_);
v___y_372_ = v___y_368_;
v___y_373_ = v_snd_389_;
goto v___jp_371_;
}
v___jp_371_:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v_fst_376_; lean_object* v_snd_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_385_; 
v___x_374_ = l_Lean_Expr_lam___override(v_x_364_, v_t_366_, v_b_367_, v_bi_365_);
v___x_375_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_374_, v___y_373_);
v_fst_376_ = lean_ctor_get(v___x_375_, 0);
v_snd_377_ = lean_ctor_get(v___x_375_, 1);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_385_ == 0)
{
v___x_379_ = v___x_375_;
v_isShared_380_ = v_isSharedCheck_385_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_snd_377_);
lean_inc(v_fst_376_);
lean_dec(v___x_375_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_385_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 1, v___y_372_);
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_fst_376_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v___y_372_);
v___x_382_ = v_reuseFailAlloc_384_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v___x_383_; 
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v_snd_377_);
return v___x_383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__8___boxed(lean_object* v_x_390_, lean_object* v_bi_391_, lean_object* v_t_392_, lean_object* v_b_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
uint8_t v_bi_boxed_397_; uint8_t v___y_25409__boxed_398_; lean_object* v_res_399_; 
v_bi_boxed_397_ = lean_unbox(v_bi_391_);
v___y_25409__boxed_398_ = lean_unbox(v___y_395_);
v_res_399_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__8(v_x_390_, v_bi_boxed_397_, v_t_392_, v_b_393_, v___y_394_, v___y_25409__boxed_398_, v___y_396_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10(lean_object* v_x_400_, lean_object* v_t_401_, lean_object* v_v_402_, lean_object* v_b_403_, uint8_t v_nondep_404_, lean_object* v___y_405_, uint8_t v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___y_409_; lean_object* v___y_410_; 
if (v___y_406_ == 0)
{
v___y_409_ = v___y_405_;
v___y_410_ = v___y_407_;
goto v___jp_408_;
}
else
{
lean_object* v___x_423_; lean_object* v_snd_424_; lean_object* v___x_425_; lean_object* v_snd_426_; lean_object* v___x_427_; lean_object* v_snd_428_; 
lean_inc_ref(v_t_401_);
v___x_423_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_t_401_, v___y_406_, v___y_407_);
v_snd_424_ = lean_ctor_get(v___x_423_, 1);
lean_inc(v_snd_424_);
lean_dec_ref(v___x_423_);
lean_inc_ref(v_v_402_);
v___x_425_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_v_402_, v___y_406_, v_snd_424_);
v_snd_426_ = lean_ctor_get(v___x_425_, 1);
lean_inc(v_snd_426_);
lean_dec_ref(v___x_425_);
lean_inc_ref(v_b_403_);
v___x_427_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_b_403_, v___y_406_, v_snd_426_);
v_snd_428_ = lean_ctor_get(v___x_427_, 1);
lean_inc(v_snd_428_);
lean_dec_ref(v___x_427_);
v___y_409_ = v___y_405_;
v___y_410_ = v_snd_428_;
goto v___jp_408_;
}
v___jp_408_:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v_fst_413_; lean_object* v_snd_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_422_; 
v___x_411_ = l_Lean_Expr_letE___override(v_x_400_, v_t_401_, v_v_402_, v_b_403_, v_nondep_404_);
v___x_412_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_411_, v___y_410_);
v_fst_413_ = lean_ctor_get(v___x_412_, 0);
v_snd_414_ = lean_ctor_get(v___x_412_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_422_ == 0)
{
v___x_416_ = v___x_412_;
v_isShared_417_ = v_isSharedCheck_422_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_snd_414_);
lean_inc(v_fst_413_);
lean_dec(v___x_412_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_422_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v___y_409_);
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_fst_413_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v___y_409_);
v___x_419_ = v_reuseFailAlloc_421_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_420_; 
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v_snd_414_);
return v___x_420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10___boxed(lean_object* v_x_429_, lean_object* v_t_430_, lean_object* v_v_431_, lean_object* v_b_432_, lean_object* v_nondep_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
uint8_t v_nondep_boxed_437_; uint8_t v___y_25458__boxed_438_; lean_object* v_res_439_; 
v_nondep_boxed_437_ = lean_unbox(v_nondep_433_);
v___y_25458__boxed_438_ = lean_unbox(v___y_435_);
v_res_439_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10(v_x_429_, v_t_430_, v_v_431_, v_b_432_, v_nondep_boxed_437_, v___y_434_, v___y_25458__boxed_438_, v___y_436_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__7(lean_object* v_f_440_, lean_object* v_a_441_, lean_object* v___y_442_, uint8_t v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___y_446_; lean_object* v___y_447_; 
if (v___y_443_ == 0)
{
v___y_446_ = v___y_442_;
v___y_447_ = v___y_444_;
goto v___jp_445_;
}
else
{
lean_object* v___x_460_; lean_object* v_snd_461_; lean_object* v___x_462_; lean_object* v_snd_463_; 
lean_inc_ref(v_f_440_);
v___x_460_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_f_440_, v___y_443_, v___y_444_);
v_snd_461_ = lean_ctor_get(v___x_460_, 1);
lean_inc(v_snd_461_);
lean_dec_ref(v___x_460_);
lean_inc_ref(v_a_441_);
v___x_462_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(v_a_441_, v___y_443_, v_snd_461_);
v_snd_463_ = lean_ctor_get(v___x_462_, 1);
lean_inc(v_snd_463_);
lean_dec_ref(v___x_462_);
v___y_446_ = v___y_442_;
v___y_447_ = v_snd_463_;
goto v___jp_445_;
}
v___jp_445_:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v_fst_450_; lean_object* v_snd_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_459_; 
v___x_448_ = l_Lean_Expr_app___override(v_f_440_, v_a_441_);
v___x_449_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_448_, v___y_447_);
v_fst_450_ = lean_ctor_get(v___x_449_, 0);
v_snd_451_ = lean_ctor_get(v___x_449_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_459_ == 0)
{
v___x_453_ = v___x_449_;
v_isShared_454_ = v_isSharedCheck_459_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_snd_451_);
lean_inc(v_fst_450_);
lean_dec(v___x_449_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_459_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 1, v___y_446_);
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_fst_450_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v___y_446_);
v___x_456_ = v_reuseFailAlloc_458_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; 
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v_snd_451_);
return v___x_457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__7___boxed(lean_object* v_f_464_, lean_object* v_a_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
uint8_t v___y_25512__boxed_469_; lean_object* v_res_470_; 
v___y_25512__boxed_469_ = lean_unbox(v___y_467_);
v_res_470_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__7(v_f_464_, v_a_465_, v___y_466_, v___y_25512__boxed_469_, v___y_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___redArg(lean_object* v_a_471_, lean_object* v_x_472_){
_start:
{
if (lean_obj_tag(v_x_472_) == 0)
{
lean_object* v___x_473_; 
v___x_473_ = lean_box(0);
return v___x_473_;
}
else
{
lean_object* v_key_474_; lean_object* v_value_475_; lean_object* v_tail_476_; uint8_t v___y_478_; lean_object* v_fst_481_; lean_object* v_snd_482_; lean_object* v_fst_483_; lean_object* v_snd_484_; uint8_t v___x_485_; 
v_key_474_ = lean_ctor_get(v_x_472_, 0);
v_value_475_ = lean_ctor_get(v_x_472_, 1);
v_tail_476_ = lean_ctor_get(v_x_472_, 2);
v_fst_481_ = lean_ctor_get(v_key_474_, 0);
v_snd_482_ = lean_ctor_get(v_key_474_, 1);
v_fst_483_ = lean_ctor_get(v_a_471_, 0);
v_snd_484_ = lean_ctor_get(v_a_471_, 1);
v___x_485_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_481_, v_fst_483_);
if (v___x_485_ == 0)
{
v___y_478_ = v___x_485_;
goto v___jp_477_;
}
else
{
uint8_t v___x_486_; 
v___x_486_ = lean_nat_dec_eq(v_snd_482_, v_snd_484_);
v___y_478_ = v___x_486_;
goto v___jp_477_;
}
v___jp_477_:
{
if (v___y_478_ == 0)
{
v_x_472_ = v_tail_476_;
goto _start;
}
else
{
lean_object* v___x_480_; 
lean_inc(v_value_475_);
v___x_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_480_, 0, v_value_475_);
return v___x_480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___redArg___boxed(lean_object* v_a_487_, lean_object* v_x_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___redArg(v_a_487_, v_x_488_);
lean_dec(v_x_488_);
lean_dec_ref(v_a_487_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg(lean_object* v_m_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_buckets_492_; lean_object* v_fst_493_; lean_object* v_snd_494_; lean_object* v___x_495_; uint64_t v___x_496_; uint64_t v___x_497_; uint64_t v___x_498_; uint64_t v___x_499_; uint64_t v___x_500_; uint64_t v_fold_501_; uint64_t v___x_502_; uint64_t v___x_503_; uint64_t v___x_504_; size_t v___x_505_; size_t v___x_506_; size_t v___x_507_; size_t v___x_508_; size_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_buckets_492_ = lean_ctor_get(v_m_490_, 1);
v_fst_493_ = lean_ctor_get(v_a_491_, 0);
v_snd_494_ = lean_ctor_get(v_a_491_, 1);
v___x_495_ = lean_array_get_size(v_buckets_492_);
v___x_496_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_493_);
v___x_497_ = lean_uint64_of_nat(v_snd_494_);
v___x_498_ = lean_uint64_mix_hash(v___x_496_, v___x_497_);
v___x_499_ = 32ULL;
v___x_500_ = lean_uint64_shift_right(v___x_498_, v___x_499_);
v_fold_501_ = lean_uint64_xor(v___x_498_, v___x_500_);
v___x_502_ = 16ULL;
v___x_503_ = lean_uint64_shift_right(v_fold_501_, v___x_502_);
v___x_504_ = lean_uint64_xor(v_fold_501_, v___x_503_);
v___x_505_ = lean_uint64_to_usize(v___x_504_);
v___x_506_ = lean_usize_of_nat(v___x_495_);
v___x_507_ = ((size_t)1ULL);
v___x_508_ = lean_usize_sub(v___x_506_, v___x_507_);
v___x_509_ = lean_usize_land(v___x_505_, v___x_508_);
v___x_510_ = lean_array_uget_borrowed(v_buckets_492_, v___x_509_);
v___x_511_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___redArg(v_a_491_, v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_m_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg(v_m_512_, v_a_513_);
lean_dec_ref(v_a_513_);
lean_dec_ref(v_m_512_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg(lean_object* v_keys_515_, lean_object* v_vals_516_, lean_object* v_i_517_, lean_object* v_k_518_){
_start:
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = lean_array_get_size(v_keys_515_);
v___x_520_ = lean_nat_dec_lt(v_i_517_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
lean_dec(v_i_517_);
v___x_521_ = lean_box(0);
return v___x_521_;
}
else
{
lean_object* v_k_x27_522_; uint8_t v___x_523_; 
v_k_x27_522_ = lean_array_fget_borrowed(v_keys_515_, v_i_517_);
v___x_523_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_518_, v_k_x27_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_unsigned_to_nat(1u);
v___x_525_ = lean_nat_add(v_i_517_, v___x_524_);
lean_dec(v_i_517_);
v_i_517_ = v___x_525_;
goto _start;
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_array_fget_borrowed(v_vals_516_, v_i_517_);
lean_dec(v_i_517_);
lean_inc(v___x_527_);
v___x_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg___boxed(lean_object* v_keys_529_, lean_object* v_vals_530_, lean_object* v_i_531_, lean_object* v_k_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg(v_keys_529_, v_vals_530_, v_i_531_, v_k_532_);
lean_dec_ref(v_k_532_);
lean_dec_ref(v_vals_530_);
lean_dec_ref(v_keys_529_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(lean_object* v_x_534_, size_t v_x_535_, lean_object* v_x_536_){
_start:
{
if (lean_obj_tag(v_x_534_) == 0)
{
lean_object* v_es_537_; lean_object* v___x_538_; size_t v___x_539_; size_t v___x_540_; lean_object* v_j_541_; lean_object* v___x_542_; 
v_es_537_ = lean_ctor_get(v_x_534_, 0);
v___x_538_ = lean_box(2);
v___x_539_ = ((size_t)31ULL);
v___x_540_ = lean_usize_land(v_x_535_, v___x_539_);
v_j_541_ = lean_usize_to_nat(v___x_540_);
v___x_542_ = lean_array_get_borrowed(v___x_538_, v_es_537_, v_j_541_);
lean_dec(v_j_541_);
switch(lean_obj_tag(v___x_542_))
{
case 0:
{
lean_object* v_key_543_; lean_object* v_val_544_; uint8_t v___x_545_; 
v_key_543_ = lean_ctor_get(v___x_542_, 0);
v_val_544_ = lean_ctor_get(v___x_542_, 1);
v___x_545_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_536_, v_key_543_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
v___x_546_ = lean_box(0);
return v___x_546_;
}
else
{
lean_object* v___x_547_; 
lean_inc(v_val_544_);
v___x_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_547_, 0, v_val_544_);
return v___x_547_;
}
}
case 1:
{
lean_object* v_node_548_; size_t v___x_549_; size_t v___x_550_; 
v_node_548_ = lean_ctor_get(v___x_542_, 0);
v___x_549_ = ((size_t)5ULL);
v___x_550_ = lean_usize_shift_right(v_x_535_, v___x_549_);
v_x_534_ = v_node_548_;
v_x_535_ = v___x_550_;
goto _start;
}
default: 
{
lean_object* v___x_552_; 
v___x_552_ = lean_box(0);
return v___x_552_;
}
}
}
else
{
lean_object* v_ks_553_; lean_object* v_vs_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_ks_553_ = lean_ctor_get(v_x_534_, 0);
v_vs_554_ = lean_ctor_get(v_x_534_, 1);
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg(v_ks_553_, v_vs_554_, v___x_555_, v_x_536_);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___boxed(lean_object* v_x_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
size_t v_x_25648__boxed_560_; lean_object* v_res_561_; 
v_x_25648__boxed_560_ = lean_unbox_usize(v_x_558_);
lean_dec(v_x_558_);
v_res_561_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(v_x_557_, v_x_25648__boxed_560_, v_x_559_);
lean_dec_ref(v_x_559_);
lean_dec_ref(v_x_557_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
uint64_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; 
v___x_564_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_563_);
v___x_565_ = lean_uint64_to_usize(v___x_564_);
v___x_566_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(v_x_562_, v___x_565_, v_x_563_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg___boxed(lean_object* v_x_567_, lean_object* v_x_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(v_x_567_, v_x_568_);
lean_dec_ref(v_x_568_);
lean_dec_ref(v_x_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13(lean_object* v_msg_577_, lean_object* v___y_578_, uint8_t v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___f_581_; lean_object* v___f_582_; lean_object* v___f_583_; lean_object* v___f_584_; lean_object* v___f_585_; lean_object* v___f_586_; lean_object* v___f_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___f_591_; lean_object* v___f_592_; lean_object* v___f_593_; lean_object* v___f_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___f_602_; lean_object* v___f_603_; lean_object* v___f_604_; lean_object* v___f_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_24867__overap_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___f_581_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__0));
v___f_582_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__1));
v___f_583_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__2));
v___f_584_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__3));
v___f_585_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__4));
v___f_586_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__5));
v___f_587_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__6));
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v___f_581_);
lean_ctor_set(v___x_588_, 1, v___f_582_);
v___x_589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
lean_ctor_set(v___x_589_, 1, v___f_583_);
lean_ctor_set(v___x_589_, 2, v___f_584_);
lean_ctor_set(v___x_589_, 3, v___f_585_);
lean_ctor_set(v___x_589_, 4, v___f_586_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v___f_587_);
lean_inc_ref_n(v___x_590_, 6);
v___f_591_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_591_, 0, v___x_590_);
v___f_592_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_592_, 0, v___x_590_);
v___f_593_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_593_, 0, v___x_590_);
v___f_594_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_594_, 0, v___x_590_);
v___x_595_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_595_, 0, lean_box(0));
lean_closure_set(v___x_595_, 1, lean_box(0));
lean_closure_set(v___x_595_, 2, v___x_590_);
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v___f_591_);
v___x_597_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_597_, 0, lean_box(0));
lean_closure_set(v___x_597_, 1, lean_box(0));
lean_closure_set(v___x_597_, 2, v___x_590_);
v___x_598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
lean_ctor_set(v___x_598_, 2, v___f_592_);
lean_ctor_set(v___x_598_, 3, v___f_593_);
lean_ctor_set(v___x_598_, 4, v___f_594_);
v___x_599_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_599_, 0, lean_box(0));
lean_closure_set(v___x_599_, 1, lean_box(0));
lean_closure_set(v___x_599_, 2, v___x_590_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = l_ReaderT_instMonad___redArg(v___x_600_);
lean_inc_ref_n(v___x_601_, 6);
v___f_602_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_602_, 0, v___x_601_);
v___f_603_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_603_, 0, v___x_601_);
v___f_604_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_604_, 0, v___x_601_);
v___f_605_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_605_, 0, v___x_601_);
v___x_606_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_606_, 0, lean_box(0));
lean_closure_set(v___x_606_, 1, lean_box(0));
lean_closure_set(v___x_606_, 2, v___x_601_);
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v___f_602_);
v___x_608_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_608_, 0, lean_box(0));
lean_closure_set(v___x_608_, 1, lean_box(0));
lean_closure_set(v___x_608_, 2, v___x_601_);
v___x_609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
lean_ctor_set(v___x_609_, 2, v___f_603_);
lean_ctor_set(v___x_609_, 3, v___f_604_);
lean_ctor_set(v___x_609_, 4, v___f_605_);
v___x_610_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_610_, 0, lean_box(0));
lean_closure_set(v___x_610_, 1, lean_box(0));
lean_closure_set(v___x_610_, 2, v___x_601_);
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_609_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = l_Lean_instInhabitedExpr;
v___x_613_ = l_instInhabitedOfMonad___redArg(v___x_611_, v___x_612_);
v___x_24867__overap_614_ = lean_panic_fn_borrowed(v___x_613_, v_msg_577_);
lean_dec(v___x_613_);
v___x_615_ = lean_box(v___y_579_);
v___x_616_ = lean_apply_3(v___x_24867__overap_614_, v___y_578_, v___x_615_, v___y_580_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___boxed(lean_object* v_msg_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
uint8_t v___y_25721__boxed_621_; lean_object* v_res_622_; 
v___y_25721__boxed_621_ = lean_unbox(v___y_619_);
v_res_622_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13(v_msg_617_, v___y_618_, v___y_25721__boxed_621_, v___y_620_);
return v_res_622_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_626_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__2));
v___x_627_ = lean_unsigned_to_nat(67u);
v___x_628_ = lean_unsigned_to_nat(35u);
v___x_629_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__1));
v___x_630_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0));
v___x_631_ = l_mkPanicMessageWithDecl(v___x_630_, v___x_629_, v___x_628_, v___x_627_, v___x_626_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(lean_object* v_minIndex_632_, lean_object* v___x_633_, lean_object* v___x_634_, lean_object* v_start_635_, lean_object* v_xs_636_, lean_object* v___x_637_, lean_object* v_e_638_, lean_object* v_offset_639_, lean_object* v_a_640_, uint8_t v_a_641_, lean_object* v_a_642_){
_start:
{
switch(lean_obj_tag(v_e_638_))
{
case 5:
{
lean_object* v_fn_643_; lean_object* v_arg_644_; lean_object* v___x_645_; lean_object* v_fst_646_; lean_object* v_snd_647_; lean_object* v_fst_648_; lean_object* v_snd_649_; lean_object* v___x_650_; lean_object* v_fst_651_; lean_object* v_snd_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_673_; 
v_fn_643_ = lean_ctor_get(v_e_638_, 0);
v_arg_644_ = lean_ctor_get(v_e_638_, 1);
lean_inc(v_offset_639_);
lean_inc_ref(v_fn_643_);
lean_inc_ref(v___x_633_);
v___x_645_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_632_, v___x_633_, v___x_634_, v_start_635_, v_xs_636_, v___x_637_, v_fn_643_, v_offset_639_, v_a_640_, v_a_641_, v_a_642_);
v_fst_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_fst_646_);
v_snd_647_ = lean_ctor_get(v___x_645_, 1);
lean_inc(v_snd_647_);
lean_dec_ref(v___x_645_);
v_fst_648_ = lean_ctor_get(v_fst_646_, 0);
lean_inc(v_fst_648_);
v_snd_649_ = lean_ctor_get(v_fst_646_, 1);
lean_inc(v_snd_649_);
lean_dec(v_fst_646_);
lean_inc_ref(v_arg_644_);
v___x_650_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_632_, v___x_633_, v___x_634_, v_start_635_, v_xs_636_, v___x_637_, v_arg_644_, v_offset_639_, v_snd_649_, v_a_641_, v_snd_647_);
v_fst_651_ = lean_ctor_get(v___x_650_, 0);
v_snd_652_ = lean_ctor_get(v___x_650_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_673_ == 0)
{
v___x_654_ = v___x_650_;
v_isShared_655_ = v_isSharedCheck_673_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_snd_652_);
lean_inc(v_fst_651_);
lean_dec(v___x_650_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_673_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_fst_656_; lean_object* v_snd_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_672_; 
v_fst_656_ = lean_ctor_get(v_fst_651_, 0);
v_snd_657_ = lean_ctor_get(v_fst_651_, 1);
v_isSharedCheck_672_ = !lean_is_exclusive(v_fst_651_);
if (v_isSharedCheck_672_ == 0)
{
v___x_659_ = v_fst_651_;
v_isShared_660_ = v_isSharedCheck_672_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_snd_657_);
lean_inc(v_fst_656_);
lean_dec(v_fst_651_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_672_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
uint8_t v___y_662_; uint8_t v___x_670_; 
v___x_670_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_643_, v_fst_648_);
if (v___x_670_ == 0)
{
v___y_662_ = v___x_670_;
goto v___jp_661_;
}
else
{
uint8_t v___x_671_; 
v___x_671_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_644_, v_fst_656_);
v___y_662_ = v___x_671_;
goto v___jp_661_;
}
v___jp_661_:
{
if (v___y_662_ == 0)
{
lean_object* v___x_663_; 
lean_del_object(v___x_659_);
lean_del_object(v___x_654_);
lean_dec_ref_known(v_e_638_, 2);
v___x_663_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__7(v_fst_648_, v_fst_656_, v_snd_657_, v_a_641_, v_snd_652_);
return v___x_663_;
}
else
{
lean_object* v___x_665_; 
lean_dec(v_fst_656_);
lean_dec(v_fst_648_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v_e_638_);
v___x_665_ = v___x_659_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_e_638_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_snd_657_);
v___x_665_ = v_reuseFailAlloc_669_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_667_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_665_);
v___x_667_ = v___x_654_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_snd_652_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_674_; lean_object* v_binderType_675_; lean_object* v_body_676_; uint8_t v_binderInfo_677_; lean_object* v___x_678_; lean_object* v_fst_679_; lean_object* v_snd_680_; lean_object* v_fst_681_; lean_object* v_snd_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v_fst_686_; lean_object* v_snd_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_708_; 
v_binderName_674_ = lean_ctor_get(v_e_638_, 0);
v_binderType_675_ = lean_ctor_get(v_e_638_, 1);
v_body_676_ = lean_ctor_get(v_e_638_, 2);
v_binderInfo_677_ = lean_ctor_get_uint8(v_e_638_, sizeof(void*)*3 + 8);
lean_inc(v_offset_639_);
lean_inc_ref(v_binderType_675_);
lean_inc_ref(v___x_633_);
v___x_678_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_632_, v___x_633_, v___x_634_, v_start_635_, v_xs_636_, v___x_637_, v_binderType_675_, v_offset_639_, v_a_640_, v_a_641_, v_a_642_);
v_fst_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_fst_679_);
v_snd_680_ = lean_ctor_get(v___x_678_, 1);
lean_inc(v_snd_680_);
lean_dec_ref(v___x_678_);
v_fst_681_ = lean_ctor_get(v_fst_679_, 0);
lean_inc(v_fst_681_);
v_snd_682_ = lean_ctor_get(v_fst_679_, 1);
lean_inc(v_snd_682_);
lean_dec(v_fst_679_);
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = lean_nat_add(v_offset_639_, v___x_683_);
lean_dec(v_offset_639_);
lean_inc_ref(v_body_676_);
v___x_685_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_632_, v___x_633_, v___x_634_, v_start_635_, v_xs_636_, v___x_637_, v_body_676_, v___x_684_, v_snd_682_, v_a_641_, v_snd_680_);
v_fst_686_ = lean_ctor_get(v___x_685_, 0);
v_snd_687_ = lean_ctor_get(v___x_685_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_708_ == 0)
{
v___x_689_ = v___x_685_;
v_isShared_690_ = v_isSharedCheck_708_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_snd_687_);
lean_inc(v_fst_686_);
lean_dec(v___x_685_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_708_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v_fst_691_; lean_object* v_snd_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_707_; 
v_fst_691_ = lean_ctor_get(v_fst_686_, 0);
v_snd_692_ = lean_ctor_get(v_fst_686_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_fst_686_);
if (v_isSharedCheck_707_ == 0)
{
v___x_694_ = v_fst_686_;
v_isShared_695_ = v_isSharedCheck_707_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_snd_692_);
lean_inc(v_fst_691_);
lean_dec(v_fst_686_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_707_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
uint8_t v___y_697_; uint8_t v___x_705_; 
v___x_705_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_675_, v_fst_681_);
if (v___x_705_ == 0)
{
v___y_697_ = v___x_705_;
goto v___jp_696_;
}
else
{
uint8_t v___x_706_; 
v___x_706_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_676_, v_fst_691_);
v___y_697_ = v___x_706_;
goto v___jp_696_;
}
v___jp_696_:
{
if (v___y_697_ == 0)
{
lean_object* v___x_698_; 
lean_inc(v_binderName_674_);
lean_del_object(v___x_694_);
lean_del_object(v___x_689_);
lean_dec_ref_known(v_e_638_, 3);
v___x_698_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__8(v_binderName_674_, v_binderInfo_677_, v_fst_681_, v_fst_691_, v_snd_692_, v_a_641_, v_snd_687_);
return v___x_698_;
}
else
{
lean_object* v___x_700_; 
lean_dec(v_fst_691_);
lean_dec(v_fst_681_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v_e_638_);
v___x_700_ = v___x_694_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_e_638_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_snd_692_);
v___x_700_ = v_reuseFailAlloc_704_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_700_);
v___x_702_ = v___x_689_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_snd_687_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_709_; lean_object* v_binderType_710_; lean_object* v_body_711_; uint8_t v_binderInfo_712_; lean_object* v___x_713_; lean_object* v_fst_714_; lean_object* v_snd_715_; lean_object* v_fst_716_; lean_object* v_snd_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v_fst_721_; lean_object* v_snd_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_743_; 
v_binderName_709_ = lean_ctor_get(v_e_638_, 0);
v_binderType_710_ = lean_ctor_get(v_e_638_, 1);
v_body_711_ = lean_ctor_get(v_e_638_, 2);
v_binderInfo_712_ = lean_ctor_get_uint8(v_e_638_, sizeof(void*)*3 + 8);
lean_inc(v_offset_639_);
lean_inc_ref(v_binderType_710_);
lean_inc_ref(v___x_633_);
v___x_713_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_632_, v___x_633_, v___x_634_, v_start_635_, v_xs_636_, v___x_637_, v_binderType_710_, v_offset_639_, v_a_640_, v_a_641_, v_a_642_);
v_fst_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_fst_714_);
v_snd_715_ = lean_ctor_get(v___x_713_, 1);
lean_inc(v_snd_715_);
lean_dec_ref(v___x_713_);
v_fst_716_ = lean_ctor_get(v_fst_714_, 0);
lean_inc(v_fst_716_);
v_snd_717_ = lean_ctor_get(v_fst_714_, 1);
lean_inc(v_snd_717_);
lean_dec(v_fst_714_);
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = lean_nat_add(v_offset_639_, v___x_718_);
lean_dec(v_offset_639_);
lean_inc_ref(v_body_711_);
v___x_720_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_632_, v___x_633_, v___x_634_, v_start_635_, v_xs_636_, v___x_637_, v_body_711_, v___x_719_, v_snd_717_, v_a_641_, v_snd_715_);
v_fst_721_ = lean_ctor_get(v___x_720_, 0);
v_snd_722_ = lean_ctor_get(v___x_720_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_743_ == 0)
{
v___x_724_ = v___x_720_;
v_isShared_725_ = v_isSharedCheck_743_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_snd_722_);
lean_inc(v_fst_721_);
lean_dec(v___x_720_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_743_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v_fst_726_; lean_object* v_snd_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_742_; 
v_fst_726_ = lean_ctor_get(v_fst_721_, 0);
v_snd_727_ = lean_ctor_get(v_fst_721_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v_fst_721_);
if (v_isSharedCheck_742_ == 0)
{
v___x_729_ = v_fst_721_;
v_isShared_730_ = v_isSharedCheck_742_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_snd_727_);
lean_inc(v_fst_726_);
lean_dec(v_fst_721_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_742_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
uint8_t v___y_732_; uint8_t v___x_740_; 
v___x_740_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_710_, v_fst_716_);
if (v___x_740_ == 0)
{
v___y_732_ = v___x_740_;
goto v___jp_731_;
}
else
{
uint8_t v___x_741_; 
v___x_741_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_711_, v_fst_726_);
v___y_732_ = v___x_741_;
goto v___jp_731_;
}
v___jp_731_:
{
if (v___y_732_ == 0)
{
lean_object* v___x_733_; 
lean_inc(v_binderName_709_);
lean_del_object(v___x_729_);
lean_del_object(v___x_724_);
lean_dec_ref_known(v_e_638_, 3);
v___x_733_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__9(v_binderName_709_, v_binderInfo_712_, v_fst_716_, v_fst_726_, v_snd_727_, v_a_641_, v_snd_722_);
return v___x_733_;
}
else
{
lean_object* v___x_735_; 
lean_dec(v_fst_726_);
lean_dec(v_fst_716_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v_e_638_);
v___x_735_ = v___x_729_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_e_638_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_snd_727_);
v___x_735_ = v_reuseFailAlloc_739_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_737_; 
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_735_);
v___x_737_ = v___x_724_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_snd_722_);
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
}
}
}
case 8:
{
lean_object* v_declName_744_; lean_object* v_type_745_; lean_object* v_value_746_; lean_object* v_body_747_; uint8_t v_nondep_748_; lean_object* v___x_749_; lean_object* v_fst_750_; lean_object* v_snd_751_; lean_object* v_fst_752_; lean_object* v_snd_753_; lean_object* v___x_754_; lean_object* v_fst_755_; lean_object* v_snd_756_; lean_object* v_fst_757_; lean_object* v_snd_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v_fst_762_; lean_object* v_snd_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_786_; 
v_declName_744_ = lean_ctor_get(v_e_638_, 0);
v_type_745_ = lean_ctor_get(v_e_638_, 1);
v_value_746_ = lean_ctor_get(v_e_638_, 2);
v_body_747_ = lean_ctor_get(v_e_638_, 3);
v_nondep_748_ = lean_ctor_get_uint8(v_e_638_, sizeof(void*)*4 + 8);
lean_inc_n(v_offset_639_, 2);
lean_inc_ref(v_type_745_);
lean_inc_ref_n(v___x_633_, 2);
v___x_749_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_632_, v___x_633_, v___x_634_, v_start_635_, v_xs_636_, v___x_637_, v_type_745_, v_offset_639_, v_a_640_, v_a_641_, v_a_642_);
v_fst_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_fst_750_);
v_snd_751_ = lean_ctor_get(v___x_749_, 1);
lean_inc(v_snd_751_);
lean_dec_ref(v___x_749_);
v_fst_752_ = lean_ctor_get(v_fst_750_, 0);
lean_inc(v_fst_752_);
v_snd_753_ = lean_ctor_get(v_fst_750_, 1);
lean_inc(v_snd_753_);
lean_dec(v_fst_750_);
lean_inc_ref(v_value_746_);
v___x_754_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_632_, v___x_633_, v___x_634_, v_start_635_, v_xs_636_, v___x_637_, v_value_746_, v_offset_639_, v_snd_753_, v_a_641_, v_snd_751_);
v_fst_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_fst_755_);
v_snd_756_ = lean_ctor_get(v___x_754_, 1);
lean_inc(v_snd_756_);
lean_dec_ref(v___x_754_);
v_fst_757_ = lean_ctor_get(v_fst_755_, 0);
lean_inc(v_fst_757_);
v_snd_758_ = lean_ctor_get(v_fst_755_, 1);
lean_inc(v_snd_758_);
lean_dec(v_fst_755_);
v___x_759_ = lean_unsigned_to_nat(1u);
v___x_760_ = lean_nat_add(v_offset_639_, v___x_759_);
lean_dec(v_offset_639_);
lean_inc_ref(v_body_747_);
v___x_761_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_632_, v___x_633_, v___x_634_, v_start_635_, v_xs_636_, v___x_637_, v_body_747_, v___x_760_, v_snd_758_, v_a_641_, v_snd_756_);
v_fst_762_ = lean_ctor_get(v___x_761_, 0);
v_snd_763_ = lean_ctor_get(v___x_761_, 1);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_786_ == 0)
{
v___x_765_ = v___x_761_;
v_isShared_766_ = v_isSharedCheck_786_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_snd_763_);
lean_inc(v_fst_762_);
lean_dec(v___x_761_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_786_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v_fst_767_; lean_object* v_snd_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_785_; 
v_fst_767_ = lean_ctor_get(v_fst_762_, 0);
v_snd_768_ = lean_ctor_get(v_fst_762_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v_fst_762_);
if (v_isSharedCheck_785_ == 0)
{
v___x_770_ = v_fst_762_;
v_isShared_771_ = v_isSharedCheck_785_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_snd_768_);
lean_inc(v_fst_767_);
lean_dec(v_fst_762_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_785_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
uint8_t v___y_773_; uint8_t v___x_783_; 
v___x_783_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_745_, v_fst_752_);
if (v___x_783_ == 0)
{
v___y_773_ = v___x_783_;
goto v___jp_772_;
}
else
{
uint8_t v___x_784_; 
v___x_784_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_746_, v_fst_757_);
v___y_773_ = v___x_784_;
goto v___jp_772_;
}
v___jp_772_:
{
if (v___y_773_ == 0)
{
lean_object* v___x_774_; 
lean_inc(v_declName_744_);
lean_del_object(v___x_770_);
lean_del_object(v___x_765_);
lean_dec_ref_known(v_e_638_, 4);
v___x_774_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10(v_declName_744_, v_fst_752_, v_fst_757_, v_fst_767_, v_nondep_748_, v_snd_768_, v_a_641_, v_snd_763_);
return v___x_774_;
}
else
{
uint8_t v___x_775_; 
v___x_775_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_747_, v_fst_767_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
lean_inc(v_declName_744_);
lean_del_object(v___x_770_);
lean_del_object(v___x_765_);
lean_dec_ref_known(v_e_638_, 4);
v___x_776_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10(v_declName_744_, v_fst_752_, v_fst_757_, v_fst_767_, v_nondep_748_, v_snd_768_, v_a_641_, v_snd_763_);
return v___x_776_;
}
else
{
lean_object* v___x_778_; 
lean_dec(v_fst_767_);
lean_dec(v_fst_757_);
lean_dec(v_fst_752_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v_e_638_);
v___x_778_ = v___x_770_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_e_638_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_snd_768_);
v___x_778_ = v_reuseFailAlloc_782_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_780_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_778_);
v___x_780_ = v___x_765_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_snd_763_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
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
lean_object* v_data_787_; lean_object* v_expr_788_; lean_object* v___x_789_; lean_object* v_fst_790_; lean_object* v_snd_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_809_; 
v_data_787_ = lean_ctor_get(v_e_638_, 0);
v_expr_788_ = lean_ctor_get(v_e_638_, 1);
lean_inc_ref(v_expr_788_);
v___x_789_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_632_, v___x_633_, v___x_634_, v_start_635_, v_xs_636_, v___x_637_, v_expr_788_, v_offset_639_, v_a_640_, v_a_641_, v_a_642_);
v_fst_790_ = lean_ctor_get(v___x_789_, 0);
v_snd_791_ = lean_ctor_get(v___x_789_, 1);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_809_ == 0)
{
v___x_793_ = v___x_789_;
v_isShared_794_ = v_isSharedCheck_809_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_snd_791_);
lean_inc(v_fst_790_);
lean_dec(v___x_789_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_809_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v_fst_795_; lean_object* v_snd_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_808_; 
v_fst_795_ = lean_ctor_get(v_fst_790_, 0);
v_snd_796_ = lean_ctor_get(v_fst_790_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v_fst_790_);
if (v_isSharedCheck_808_ == 0)
{
v___x_798_ = v_fst_790_;
v_isShared_799_ = v_isSharedCheck_808_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_snd_796_);
lean_inc(v_fst_795_);
lean_dec(v_fst_790_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_808_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
uint8_t v___x_800_; 
v___x_800_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_788_, v_fst_795_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; 
lean_inc(v_data_787_);
lean_del_object(v___x_798_);
lean_del_object(v___x_793_);
lean_dec_ref_known(v_e_638_, 2);
v___x_801_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__11(v_data_787_, v_fst_795_, v_snd_796_, v_a_641_, v_snd_791_);
return v___x_801_;
}
else
{
lean_object* v___x_803_; 
lean_dec(v_fst_795_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v_e_638_);
v___x_803_ = v___x_798_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_e_638_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_snd_796_);
v___x_803_ = v_reuseFailAlloc_807_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_805_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_803_);
v___x_805_ = v___x_793_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_snd_791_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_810_; lean_object* v_idx_811_; lean_object* v_struct_812_; lean_object* v___x_813_; lean_object* v_fst_814_; lean_object* v_snd_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_833_; 
v_typeName_810_ = lean_ctor_get(v_e_638_, 0);
v_idx_811_ = lean_ctor_get(v_e_638_, 1);
v_struct_812_ = lean_ctor_get(v_e_638_, 2);
lean_inc_ref(v_struct_812_);
v___x_813_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_632_, v___x_633_, v___x_634_, v_start_635_, v_xs_636_, v___x_637_, v_struct_812_, v_offset_639_, v_a_640_, v_a_641_, v_a_642_);
v_fst_814_ = lean_ctor_get(v___x_813_, 0);
v_snd_815_ = lean_ctor_get(v___x_813_, 1);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_833_ == 0)
{
v___x_817_ = v___x_813_;
v_isShared_818_ = v_isSharedCheck_833_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_snd_815_);
lean_inc(v_fst_814_);
lean_dec(v___x_813_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_833_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v_fst_819_; lean_object* v_snd_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_832_; 
v_fst_819_ = lean_ctor_get(v_fst_814_, 0);
v_snd_820_ = lean_ctor_get(v_fst_814_, 1);
v_isSharedCheck_832_ = !lean_is_exclusive(v_fst_814_);
if (v_isSharedCheck_832_ == 0)
{
v___x_822_ = v_fst_814_;
v_isShared_823_ = v_isSharedCheck_832_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_snd_820_);
lean_inc(v_fst_819_);
lean_dec(v_fst_814_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_832_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
uint8_t v___x_824_; 
v___x_824_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_812_, v_fst_819_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; 
lean_inc(v_idx_811_);
lean_inc(v_typeName_810_);
lean_del_object(v___x_822_);
lean_del_object(v___x_817_);
lean_dec_ref_known(v_e_638_, 3);
v___x_825_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__12(v_typeName_810_, v_idx_811_, v_fst_819_, v_snd_820_, v_a_641_, v_snd_815_);
return v___x_825_;
}
else
{
lean_object* v___x_827_; 
lean_dec(v_fst_819_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v_e_638_);
v___x_827_ = v___x_822_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_e_638_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_snd_820_);
v___x_827_ = v_reuseFailAlloc_831_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_829_; 
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_827_);
v___x_829_ = v___x_817_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_snd_815_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec(v_offset_639_);
lean_dec_ref(v_e_638_);
lean_dec_ref(v___x_633_);
v___x_834_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3);
v___x_835_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13(v___x_834_, v_a_640_, v_a_641_, v_a_642_);
return v___x_835_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(lean_object* v_minIndex_836_, lean_object* v___x_837_, lean_object* v___x_838_, lean_object* v_start_839_, lean_object* v_xs_840_, lean_object* v___x_841_, lean_object* v_e_842_, lean_object* v_offset_843_, lean_object* v_a_844_, uint8_t v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_key_847_; lean_object* v_snd_849_; lean_object* v___y_863_; lean_object* v___y_868_; lean_object* v___x_873_; 
lean_inc(v_offset_843_);
lean_inc_ref(v_e_842_);
v_key_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_847_, 0, v_e_842_);
lean_ctor_set(v_key_847_, 1, v_offset_843_);
v___x_873_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg(v_a_844_, v_key_847_);
if (lean_obj_tag(v___x_873_) == 1)
{
lean_object* v_val_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec_ref_known(v_key_847_, 2);
lean_dec(v_offset_843_);
lean_dec_ref(v_e_842_);
lean_dec_ref(v___x_837_);
v_val_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_val_874_);
lean_dec_ref_known(v___x_873_, 1);
v___x_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_875_, 0, v_val_874_);
lean_ctor_set(v___x_875_, 1, v_a_844_);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v_a_846_);
return v___x_876_;
}
else
{
lean_dec(v___x_873_);
switch(lean_obj_tag(v_e_842_))
{
case 1:
{
lean_object* v_fvarId_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec_ref(v___x_837_);
v_fvarId_877_ = lean_ctor_get(v_e_842_, 0);
v___x_878_ = lean_unsigned_to_nat(0u);
v___x_879_ = lean_unsigned_to_nat(1u);
v___x_880_ = lean_nat_sub(v___x_838_, v___x_879_);
v___x_881_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_839_, v_xs_840_, v_fvarId_877_, v___x_878_, v___x_880_);
if (lean_obj_tag(v___x_881_) == 1)
{
lean_object* v_val_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v_fst_885_; lean_object* v_snd_886_; lean_object* v___x_887_; 
lean_dec_ref_known(v_e_842_, 1);
v_val_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_val_882_);
lean_dec_ref_known(v___x_881_, 1);
v___x_883_ = lean_nat_add(v_offset_843_, v_val_882_);
lean_dec(v_val_882_);
lean_dec(v_offset_843_);
v___x_884_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v___x_883_, v_a_846_);
v_fst_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_fst_885_);
v_snd_886_ = lean_ctor_get(v___x_884_, 1);
lean_inc(v_snd_886_);
lean_dec_ref(v___x_884_);
v___x_887_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_847_, v_fst_885_, v_a_844_, v_a_845_, v_snd_886_);
return v___x_887_;
}
else
{
lean_object* v___x_888_; 
lean_dec(v___x_881_);
lean_dec(v_offset_843_);
v___x_888_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_847_, v_e_842_, v_a_844_, v_a_845_, v_a_846_);
return v___x_888_;
}
}
case 9:
{
lean_object* v___x_889_; 
lean_dec(v_offset_843_);
lean_dec_ref(v___x_837_);
v___x_889_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_847_, v_e_842_, v_a_844_, v_a_845_, v_a_846_);
return v___x_889_;
}
case 2:
{
lean_object* v___x_890_; 
lean_dec(v_offset_843_);
lean_dec_ref(v___x_837_);
v___x_890_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_847_, v_e_842_, v_a_844_, v_a_845_, v_a_846_);
return v___x_890_;
}
case 0:
{
lean_object* v___x_891_; 
lean_dec(v_offset_843_);
lean_dec_ref(v___x_837_);
v___x_891_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_847_, v_e_842_, v_a_844_, v_a_845_, v_a_846_);
return v___x_891_;
}
case 4:
{
lean_object* v___x_892_; 
lean_dec(v_offset_843_);
lean_dec_ref(v___x_837_);
v___x_892_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_847_, v_e_842_, v_a_844_, v_a_845_, v_a_846_);
return v___x_892_;
}
case 3:
{
lean_object* v___x_893_; 
lean_dec(v_offset_843_);
lean_dec_ref(v___x_837_);
v___x_893_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_847_, v_e_842_, v_a_844_, v_a_845_, v_a_846_);
return v___x_893_;
}
default: 
{
uint8_t v___x_894_; 
v___x_894_ = l_Lean_Expr_hasFVar(v_e_842_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; 
lean_dec(v_offset_843_);
lean_dec_ref(v___x_837_);
v___x_895_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_847_, v_e_842_, v_a_844_, v_a_845_, v_a_846_);
return v___x_895_;
}
else
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(v___x_841_, v_e_842_);
if (lean_obj_tag(v___x_896_) == 1)
{
lean_object* v_val_897_; 
v_val_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_val_897_);
lean_dec_ref_known(v___x_896_, 1);
if (lean_obj_tag(v_val_897_) == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_899_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v___x_898_);
v___y_868_ = v___x_899_;
goto v___jp_867_;
}
else
{
lean_object* v_val_900_; 
v_val_900_ = lean_ctor_get(v_val_897_, 0);
lean_inc(v_val_900_);
lean_dec_ref_known(v_val_897_, 1);
v___y_868_ = v_val_900_;
goto v___jp_867_;
}
}
else
{
lean_dec(v___x_896_);
v_snd_849_ = v_a_846_;
goto v___jp_848_;
}
}
}
}
}
v___jp_848_:
{
switch(lean_obj_tag(v_e_842_))
{
case 9:
{
lean_object* v___x_850_; 
lean_dec(v_offset_843_);
lean_dec_ref(v___x_837_);
v___x_850_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_847_, v_e_842_, v_a_844_, v_a_845_, v_snd_849_);
return v___x_850_;
}
case 2:
{
lean_object* v___x_851_; 
lean_dec(v_offset_843_);
lean_dec_ref(v___x_837_);
v___x_851_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_847_, v_e_842_, v_a_844_, v_a_845_, v_snd_849_);
return v___x_851_;
}
case 0:
{
lean_object* v___x_852_; 
lean_dec(v_offset_843_);
lean_dec_ref(v___x_837_);
v___x_852_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_847_, v_e_842_, v_a_844_, v_a_845_, v_snd_849_);
return v___x_852_;
}
case 1:
{
lean_object* v___x_853_; 
lean_dec(v_offset_843_);
lean_dec_ref(v___x_837_);
v___x_853_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_847_, v_e_842_, v_a_844_, v_a_845_, v_snd_849_);
return v___x_853_;
}
case 4:
{
lean_object* v___x_854_; 
lean_dec(v_offset_843_);
lean_dec_ref(v___x_837_);
v___x_854_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_847_, v_e_842_, v_a_844_, v_a_845_, v_snd_849_);
return v___x_854_;
}
case 3:
{
lean_object* v___x_855_; 
lean_dec(v_offset_843_);
lean_dec_ref(v___x_837_);
v___x_855_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_847_, v_e_842_, v_a_844_, v_a_845_, v_snd_849_);
return v___x_855_;
}
default: 
{
lean_object* v___x_856_; lean_object* v_fst_857_; lean_object* v_snd_858_; lean_object* v_fst_859_; lean_object* v_snd_860_; lean_object* v___x_861_; 
v___x_856_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v_minIndex_836_, v___x_837_, v___x_838_, v_start_839_, v_xs_840_, v___x_841_, v_e_842_, v_offset_843_, v_a_844_, v_a_845_, v_snd_849_);
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
v___x_861_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_847_, v_fst_859_, v_snd_860_, v_a_845_, v_snd_858_);
return v___x_861_;
}
}
}
v___jp_862_:
{
lean_object* v_maxIndex_864_; uint8_t v___x_865_; 
v_maxIndex_864_ = l_Lean_LocalDecl_index(v___y_863_);
lean_dec_ref(v___y_863_);
v___x_865_ = lean_nat_dec_lt(v_maxIndex_864_, v_minIndex_836_);
lean_dec(v_maxIndex_864_);
if (v___x_865_ == 0)
{
v_snd_849_ = v_a_846_;
goto v___jp_848_;
}
else
{
lean_object* v___x_866_; 
lean_dec(v_offset_843_);
lean_dec_ref(v___x_837_);
v___x_866_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_847_, v_e_842_, v_a_844_, v_a_845_, v_a_846_);
return v___x_866_;
}
}
v___jp_867_:
{
lean_object* v___x_869_; 
lean_inc_ref(v___x_837_);
v___x_869_ = lean_local_ctx_find(v___x_837_, v___y_868_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_871_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v___x_870_);
v___y_863_ = v___x_871_;
goto v___jp_862_;
}
else
{
lean_object* v_val_872_; 
v_val_872_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_val_872_);
lean_dec_ref_known(v___x_869_, 1);
v___y_863_ = v_val_872_;
goto v___jp_862_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6___boxed(lean_object* v_minIndex_901_, lean_object* v___x_902_, lean_object* v___x_903_, lean_object* v_start_904_, lean_object* v_xs_905_, lean_object* v___x_906_, lean_object* v_e_907_, lean_object* v_offset_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
uint8_t v_a_boxed_912_; lean_object* v_res_913_; 
v_a_boxed_912_ = lean_unbox(v_a_910_);
v_res_913_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_901_, v___x_902_, v___x_903_, v_start_904_, v_xs_905_, v___x_906_, v_e_907_, v_offset_908_, v_a_909_, v_a_boxed_912_, v_a_911_);
lean_dec_ref(v___x_906_);
lean_dec_ref(v_xs_905_);
lean_dec(v_start_904_);
lean_dec(v___x_903_);
lean_dec(v_minIndex_901_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___boxed(lean_object* v_minIndex_914_, lean_object* v___x_915_, lean_object* v___x_916_, lean_object* v_start_917_, lean_object* v_xs_918_, lean_object* v___x_919_, lean_object* v_e_920_, lean_object* v_offset_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
uint8_t v_a_boxed_925_; lean_object* v_res_926_; 
v_a_boxed_925_ = lean_unbox(v_a_923_);
v_res_926_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v_minIndex_914_, v___x_915_, v___x_916_, v_start_917_, v_xs_918_, v___x_919_, v_e_920_, v_offset_921_, v_a_922_, v_a_boxed_925_, v_a_924_);
lean_dec_ref(v___x_919_);
lean_dec_ref(v_xs_918_);
lean_dec(v_start_917_);
lean_dec(v___x_916_);
lean_dec(v_minIndex_914_);
return v_res_926_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0(void){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(lean_box(0));
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___redArg(lean_object* v_e_928_, lean_object* v_start_929_, lean_object* v_xs_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
uint8_t v___x_934_; 
v___x_934_ = l_Lean_Expr_hasFVar(v_e_928_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; 
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v_e_928_);
return v___x_935_;
}
else
{
lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_936_ = lean_array_get_size(v_xs_930_);
v___x_937_ = lean_nat_dec_lt(v_start_929_, v___x_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; 
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v_e_928_);
return v___x_938_;
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v_share_941_; lean_object* v_maxFVar_942_; lean_object* v_proofInstInfo_943_; lean_object* v_inferType_944_; lean_object* v_getLevel_945_; lean_object* v_congrInfo_946_; lean_object* v_defEqI_947_; lean_object* v_extensions_948_; lean_object* v_issues_949_; lean_object* v_canon_950_; uint8_t v_debug_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_1035_; 
v___x_939_ = lean_st_ref_get(v_a_931_);
v___x_940_ = lean_st_ref_take(v_a_931_);
v_share_941_ = lean_ctor_get(v___x_940_, 0);
v_maxFVar_942_ = lean_ctor_get(v___x_940_, 1);
v_proofInstInfo_943_ = lean_ctor_get(v___x_940_, 2);
v_inferType_944_ = lean_ctor_get(v___x_940_, 3);
v_getLevel_945_ = lean_ctor_get(v___x_940_, 4);
v_congrInfo_946_ = lean_ctor_get(v___x_940_, 5);
v_defEqI_947_ = lean_ctor_get(v___x_940_, 6);
v_extensions_948_ = lean_ctor_get(v___x_940_, 7);
v_issues_949_ = lean_ctor_get(v___x_940_, 8);
v_canon_950_ = lean_ctor_get(v___x_940_, 9);
v_debug_951_ = lean_ctor_get_uint8(v___x_940_, sizeof(void*)*10);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_953_ = v___x_940_;
v_isShared_954_ = v_isSharedCheck_1035_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_canon_950_);
lean_inc(v_issues_949_);
lean_inc(v_extensions_948_);
lean_inc(v_defEqI_947_);
lean_inc(v_congrInfo_946_);
lean_inc(v_getLevel_945_);
lean_inc(v_inferType_944_);
lean_inc(v_proofInstInfo_943_);
lean_inc(v_maxFVar_942_);
lean_inc(v_share_941_);
lean_dec(v___x_940_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_1035_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v___x_957_; 
v___x_955_ = lean_obj_once(&l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0, &l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0_once, _init_l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v___x_955_);
v___x_957_ = v___x_953_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v_maxFVar_942_);
lean_ctor_set(v_reuseFailAlloc_1034_, 2, v_proofInstInfo_943_);
lean_ctor_set(v_reuseFailAlloc_1034_, 3, v_inferType_944_);
lean_ctor_set(v_reuseFailAlloc_1034_, 4, v_getLevel_945_);
lean_ctor_set(v_reuseFailAlloc_1034_, 5, v_congrInfo_946_);
lean_ctor_set(v_reuseFailAlloc_1034_, 6, v_defEqI_947_);
lean_ctor_set(v_reuseFailAlloc_1034_, 7, v_extensions_948_);
lean_ctor_set(v_reuseFailAlloc_1034_, 8, v_issues_949_);
lean_ctor_set(v_reuseFailAlloc_1034_, 9, v_canon_950_);
lean_ctor_set_uint8(v_reuseFailAlloc_1034_, sizeof(void*)*10, v_debug_951_);
v___x_957_ = v_reuseFailAlloc_1034_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v_fst_961_; lean_object* v_snd_962_; lean_object* v_lctx_984_; lean_object* v_maxFVar_985_; uint8_t v_debug_986_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v_snd_990_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1012_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_958_ = lean_st_ref_set(v_a_931_, v___x_957_);
v___x_959_ = lean_st_ref_get(v_a_931_);
v_lctx_984_ = lean_ctor_get(v_a_932_, 2);
v_maxFVar_985_ = lean_ctor_get(v___x_939_, 1);
lean_inc_ref(v_maxFVar_985_);
lean_dec(v___x_939_);
v_debug_986_ = lean_ctor_get_uint8(v___x_959_, sizeof(void*)*10);
lean_dec(v___x_959_);
v___x_1028_ = lean_array_fget_borrowed(v_xs_930_, v_start_929_);
v___x_1029_ = l_Lean_Expr_fvarId_x21(v___x_1028_);
lean_inc_ref(v_lctx_984_);
v___x_1030_ = lean_local_ctx_find(v_lctx_984_, v___x_1029_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1032_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v___x_1031_);
v___y_1012_ = v___x_1032_;
goto v___jp_1011_;
}
else
{
lean_object* v_val_1033_; 
v_val_1033_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_val_1033_);
lean_dec_ref_known(v___x_1030_, 1);
v___y_1012_ = v_val_1033_;
goto v___jp_1011_;
}
v___jp_960_:
{
lean_object* v___x_963_; lean_object* v_maxFVar_964_; lean_object* v_proofInstInfo_965_; lean_object* v_inferType_966_; lean_object* v_getLevel_967_; lean_object* v_congrInfo_968_; lean_object* v_defEqI_969_; lean_object* v_extensions_970_; lean_object* v_issues_971_; lean_object* v_canon_972_; uint8_t v_debug_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_982_; 
v___x_963_ = lean_st_ref_take(v_a_931_);
v_maxFVar_964_ = lean_ctor_get(v___x_963_, 1);
v_proofInstInfo_965_ = lean_ctor_get(v___x_963_, 2);
v_inferType_966_ = lean_ctor_get(v___x_963_, 3);
v_getLevel_967_ = lean_ctor_get(v___x_963_, 4);
v_congrInfo_968_ = lean_ctor_get(v___x_963_, 5);
v_defEqI_969_ = lean_ctor_get(v___x_963_, 6);
v_extensions_970_ = lean_ctor_get(v___x_963_, 7);
v_issues_971_ = lean_ctor_get(v___x_963_, 8);
v_canon_972_ = lean_ctor_get(v___x_963_, 9);
v_debug_973_ = lean_ctor_get_uint8(v___x_963_, sizeof(void*)*10);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v___x_963_, 0);
lean_dec(v_unused_983_);
v___x_975_ = v___x_963_;
v_isShared_976_ = v_isSharedCheck_982_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_canon_972_);
lean_inc(v_issues_971_);
lean_inc(v_extensions_970_);
lean_inc(v_defEqI_969_);
lean_inc(v_congrInfo_968_);
lean_inc(v_getLevel_967_);
lean_inc(v_inferType_966_);
lean_inc(v_proofInstInfo_965_);
lean_inc(v_maxFVar_964_);
lean_dec(v___x_963_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_982_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v_snd_962_);
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_snd_962_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_maxFVar_964_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_proofInstInfo_965_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v_inferType_966_);
lean_ctor_set(v_reuseFailAlloc_981_, 4, v_getLevel_967_);
lean_ctor_set(v_reuseFailAlloc_981_, 5, v_congrInfo_968_);
lean_ctor_set(v_reuseFailAlloc_981_, 6, v_defEqI_969_);
lean_ctor_set(v_reuseFailAlloc_981_, 7, v_extensions_970_);
lean_ctor_set(v_reuseFailAlloc_981_, 8, v_issues_971_);
lean_ctor_set(v_reuseFailAlloc_981_, 9, v_canon_972_);
lean_ctor_set_uint8(v_reuseFailAlloc_981_, sizeof(void*)*10, v_debug_973_);
v___x_978_ = v_reuseFailAlloc_981_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_st_ref_set(v_a_931_, v___x_978_);
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v_fst_961_);
return v___x_980_;
}
}
}
v___jp_987_:
{
switch(lean_obj_tag(v_e_928_))
{
case 9:
{
lean_dec(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v_maxFVar_985_);
v_fst_961_ = v_e_928_;
v_snd_962_ = v_snd_990_;
goto v___jp_960_;
}
case 2:
{
lean_dec(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v_maxFVar_985_);
v_fst_961_ = v_e_928_;
v_snd_962_ = v_snd_990_;
goto v___jp_960_;
}
case 0:
{
lean_dec(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v_maxFVar_985_);
v_fst_961_ = v_e_928_;
v_snd_962_ = v_snd_990_;
goto v___jp_960_;
}
case 1:
{
lean_dec(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v_maxFVar_985_);
v_fst_961_ = v_e_928_;
v_snd_962_ = v_snd_990_;
goto v___jp_960_;
}
case 4:
{
lean_dec(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v_maxFVar_985_);
v_fst_961_ = v_e_928_;
v_snd_962_ = v_snd_990_;
goto v___jp_960_;
}
case 3:
{
lean_dec(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v_maxFVar_985_);
v_fst_961_ = v_e_928_;
v_snd_962_ = v_snd_990_;
goto v___jp_960_;
}
default: 
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v_fst_994_; lean_object* v_snd_995_; lean_object* v_fst_996_; 
v___x_991_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0);
lean_inc(v___y_988_);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v___y_988_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
lean_inc_ref(v_lctx_984_);
v___x_993_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v___y_989_, v_lctx_984_, v___x_936_, v_start_929_, v_xs_930_, v_maxFVar_985_, v_e_928_, v___y_988_, v___x_992_, v_debug_986_, v_snd_990_);
lean_dec_ref(v_maxFVar_985_);
lean_dec(v___y_989_);
v_fst_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_fst_994_);
v_snd_995_ = lean_ctor_get(v___x_993_, 1);
lean_inc(v_snd_995_);
lean_dec_ref(v___x_993_);
v_fst_996_ = lean_ctor_get(v_fst_994_, 0);
lean_inc(v_fst_996_);
lean_dec(v_fst_994_);
v_fst_961_ = v_fst_996_;
v_snd_962_ = v_snd_995_;
goto v___jp_960_;
}
}
}
v___jp_997_:
{
lean_object* v_maxIndex_1001_; uint8_t v___x_1002_; 
v_maxIndex_1001_ = l_Lean_LocalDecl_index(v___y_1000_);
lean_dec_ref(v___y_1000_);
v___x_1002_ = lean_nat_dec_lt(v_maxIndex_1001_, v___y_999_);
lean_dec(v_maxIndex_1001_);
if (v___x_1002_ == 0)
{
v___y_988_ = v___y_998_;
v___y_989_ = v___y_999_;
v_snd_990_ = v_share_941_;
goto v___jp_987_;
}
else
{
lean_dec(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v_maxFVar_985_);
v_fst_961_ = v_e_928_;
v_snd_962_ = v_share_941_;
goto v___jp_960_;
}
}
v___jp_1003_:
{
lean_object* v___x_1007_; 
lean_inc_ref(v_lctx_984_);
v___x_1007_ = lean_local_ctx_find(v_lctx_984_, v___y_1006_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1009_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v___x_1008_);
v___y_998_ = v___y_1004_;
v___y_999_ = v___y_1005_;
v___y_1000_ = v___x_1009_;
goto v___jp_997_;
}
else
{
lean_object* v_val_1010_; 
v_val_1010_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_val_1010_);
lean_dec_ref_known(v___x_1007_, 1);
v___y_998_ = v___y_1004_;
v___y_999_ = v___y_1005_;
v___y_1000_ = v_val_1010_;
goto v___jp_997_;
}
}
v___jp_1011_:
{
lean_object* v___x_1013_; 
v___x_1013_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_928_))
{
case 1:
{
lean_object* v_fvarId_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec_ref(v___y_1012_);
lean_dec_ref(v_maxFVar_985_);
v_fvarId_1014_ = lean_ctor_get(v_e_928_, 0);
v___x_1015_ = lean_unsigned_to_nat(1u);
v___x_1016_ = lean_nat_sub(v___x_936_, v___x_1015_);
v___x_1017_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_929_, v_xs_930_, v_fvarId_1014_, v___x_1013_, v___x_1016_);
if (lean_obj_tag(v___x_1017_) == 1)
{
lean_object* v_val_1018_; lean_object* v___x_1019_; lean_object* v_fst_1020_; lean_object* v_snd_1021_; 
lean_dec_ref_known(v_e_928_, 1);
v_val_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_val_1018_);
lean_dec_ref_known(v___x_1017_, 1);
v___x_1019_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_val_1018_, v_share_941_);
v_fst_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_fst_1020_);
v_snd_1021_ = lean_ctor_get(v___x_1019_, 1);
lean_inc(v_snd_1021_);
lean_dec_ref(v___x_1019_);
v_fst_961_ = v_fst_1020_;
v_snd_962_ = v_snd_1021_;
goto v___jp_960_;
}
else
{
lean_dec(v___x_1017_);
v_fst_961_ = v_e_928_;
v_snd_962_ = v_share_941_;
goto v___jp_960_;
}
}
case 9:
{
lean_dec_ref(v___y_1012_);
lean_dec_ref(v_maxFVar_985_);
v_fst_961_ = v_e_928_;
v_snd_962_ = v_share_941_;
goto v___jp_960_;
}
case 2:
{
lean_dec_ref(v___y_1012_);
lean_dec_ref(v_maxFVar_985_);
v_fst_961_ = v_e_928_;
v_snd_962_ = v_share_941_;
goto v___jp_960_;
}
case 0:
{
lean_dec_ref(v___y_1012_);
lean_dec_ref(v_maxFVar_985_);
v_fst_961_ = v_e_928_;
v_snd_962_ = v_share_941_;
goto v___jp_960_;
}
case 4:
{
lean_dec_ref(v___y_1012_);
lean_dec_ref(v_maxFVar_985_);
v_fst_961_ = v_e_928_;
v_snd_962_ = v_share_941_;
goto v___jp_960_;
}
case 3:
{
lean_dec_ref(v___y_1012_);
lean_dec_ref(v_maxFVar_985_);
v_fst_961_ = v_e_928_;
v_snd_962_ = v_share_941_;
goto v___jp_960_;
}
default: 
{
if (v___x_934_ == 0)
{
lean_dec_ref(v___y_1012_);
lean_dec_ref(v_maxFVar_985_);
v_fst_961_ = v_e_928_;
v_snd_962_ = v_share_941_;
goto v___jp_960_;
}
else
{
lean_object* v_minIndex_1022_; lean_object* v___x_1023_; 
v_minIndex_1022_ = l_Lean_LocalDecl_index(v___y_1012_);
lean_dec_ref(v___y_1012_);
v___x_1023_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(v_maxFVar_985_, v_e_928_);
if (lean_obj_tag(v___x_1023_) == 1)
{
lean_object* v_val_1024_; 
v_val_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_val_1024_);
lean_dec_ref_known(v___x_1023_, 1);
if (lean_obj_tag(v_val_1024_) == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1026_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v___x_1025_);
v___y_1004_ = v___x_1013_;
v___y_1005_ = v_minIndex_1022_;
v___y_1006_ = v___x_1026_;
goto v___jp_1003_;
}
else
{
lean_object* v_val_1027_; 
v_val_1027_ = lean_ctor_get(v_val_1024_, 0);
lean_inc(v_val_1027_);
lean_dec_ref_known(v_val_1024_, 1);
v___y_1004_ = v___x_1013_;
v___y_1005_ = v_minIndex_1022_;
v___y_1006_ = v_val_1027_;
goto v___jp_1003_;
}
}
else
{
lean_dec(v___x_1023_);
v___y_988_ = v___x_1013_;
v___y_989_ = v_minIndex_1022_;
v_snd_990_ = v_share_941_;
goto v___jp_987_;
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___redArg___boxed(lean_object* v_e_1036_, lean_object* v_start_1037_, lean_object* v_xs_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v_e_1036_, v_start_1037_, v_xs_1038_, v_a_1039_, v_a_1040_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_xs_1038_);
lean_dec(v_start_1037_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange(lean_object* v_e_1043_, lean_object* v_start_1044_, lean_object* v_xs_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v_e_1043_, v_start_1044_, v_xs_1045_, v_a_1047_, v_a_1048_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___boxed(lean_object* v_e_1054_, lean_object* v_start_1055_, lean_object* v_xs_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1054_, v_start_1055_, v_xs_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec_ref(v_xs_1056_);
lean_dec(v_start_1055_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(lean_object* v_00_u03b2_1065_, lean_object* v_x_1066_, lean_object* v_x_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(v_x_1066_, v_x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___boxed(lean_object* v_00_u03b2_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(v_00_u03b2_1069_, v_x_1070_, v_x_1071_);
lean_dec_ref(v_x_1071_);
lean_dec_ref(v_x_1070_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3(lean_object* v_00_u03b2_1073_, lean_object* v_x_1074_, size_t v_x_1075_, lean_object* v_x_1076_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(v_x_1074_, v_x_1075_, v_x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___boxed(lean_object* v_00_u03b2_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_){
_start:
{
size_t v_x_26607__boxed_1082_; lean_object* v_res_1083_; 
v_x_26607__boxed_1082_ = lean_unbox_usize(v_x_1080_);
lean_dec(v_x_1080_);
v_res_1083_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3(v_00_u03b2_1078_, v_x_1079_, v_x_26607__boxed_1082_, v_x_1081_);
lean_dec_ref(v_x_1081_);
lean_dec_ref(v_x_1079_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5(lean_object* v_00_u03b2_1084_, lean_object* v_keys_1085_, lean_object* v_vals_1086_, lean_object* v_heq_1087_, lean_object* v_i_1088_, lean_object* v_k_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg(v_keys_1085_, v_vals_1086_, v_i_1088_, v_k_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1091_, lean_object* v_keys_1092_, lean_object* v_vals_1093_, lean_object* v_heq_1094_, lean_object* v_i_1095_, lean_object* v_k_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5(v_00_u03b2_1091_, v_keys_1092_, v_vals_1093_, v_heq_1094_, v_i_1095_, v_k_1096_);
lean_dec_ref(v_k_1096_);
lean_dec_ref(v_vals_1093_);
lean_dec_ref(v_keys_1092_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_1098_, lean_object* v_m_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg(v_m_1099_, v_a_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1102_, lean_object* v_m_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8(v_00_u03b2_1102_, v_m_1103_, v_a_1104_);
lean_dec_ref(v_a_1104_);
lean_dec_ref(v_m_1103_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16(lean_object* v_00_u03b2_1106_, lean_object* v_a_1107_, lean_object* v_x_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___redArg(v_a_1107_, v_x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___boxed(lean_object* v_00_u03b2_1110_, lean_object* v_a_1111_, lean_object* v_x_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16(v_00_u03b2_1110_, v_a_1111_, v_x_1112_);
lean_dec(v_x_1112_);
lean_dec_ref(v_a_1111_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars___redArg(lean_object* v_e_1114_, lean_object* v_xs_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_unsigned_to_nat(0u);
v___x_1120_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v_e_1114_, v___x_1119_, v_xs_1115_, v_a_1116_, v_a_1117_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars___redArg___boxed(lean_object* v_e_1121_, lean_object* v_xs_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_Meta_Sym_abstractFVars___redArg(v_e_1121_, v_xs_1122_, v_a_1123_, v_a_1124_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_xs_1122_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars(lean_object* v_e_1127_, lean_object* v_xs_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_unsigned_to_nat(0u);
v___x_1137_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v_e_1127_, v___x_1136_, v_xs_1128_, v_a_1130_, v_a_1131_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars___boxed(lean_object* v_e_1138_, lean_object* v_xs_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_Meta_Sym_abstractFVars(v_e_1138_, v_xs_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec_ref(v_xs_1139_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(lean_object* v_x_1148_, uint8_t v_bi_1149_, lean_object* v_t_1150_, lean_object* v_b_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___y_1160_; lean_object* v___x_1163_; uint8_t v_debug_1164_; 
v___x_1163_ = lean_st_ref_get(v___y_1153_);
v_debug_1164_ = lean_ctor_get_uint8(v___x_1163_, sizeof(void*)*10);
lean_dec(v___x_1163_);
if (v_debug_1164_ == 0)
{
v___y_1160_ = v___y_1153_;
goto v___jp_1159_;
}
else
{
lean_object* v___x_1165_; 
lean_inc_ref(v_t_1150_);
v___x_1165_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1150_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v___x_1166_; 
lean_dec_ref_known(v___x_1165_, 1);
lean_inc_ref(v_b_1151_);
v___x_1166_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_dec_ref_known(v___x_1166_, 1);
v___y_1160_ = v___y_1153_;
goto v___jp_1159_;
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec_ref(v_b_1151_);
lean_dec_ref(v_t_1150_);
lean_dec(v_x_1148_);
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec_ref(v_b_1151_);
lean_dec_ref(v_t_1150_);
lean_dec(v_x_1148_);
v_a_1175_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1165_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1165_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
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
v___jp_1159_:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = l_Lean_Expr_lam___override(v_x_1148_, v_t_1150_, v_b_1151_, v_bi_1149_);
v___x_1162_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1161_, v___y_1160_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0___boxed(lean_object* v_x_1183_, lean_object* v_bi_1184_, lean_object* v_t_1185_, lean_object* v_b_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
uint8_t v_bi_boxed_1194_; lean_object* v_res_1195_; 
v_bi_boxed_1194_ = lean_unbox(v_bi_1184_);
v_res_1195_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v_x_1183_, v_bi_boxed_1194_, v_t_1185_, v_b_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(lean_object* v_xs_1196_, lean_object* v_i_1197_, lean_object* v_a_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_zero_1206_; uint8_t v_isZero_1207_; 
v_zero_1206_ = lean_unsigned_to_nat(0u);
v_isZero_1207_ = lean_nat_dec_eq(v_i_1197_, v_zero_1206_);
if (v_isZero_1207_ == 1)
{
lean_object* v___x_1208_; 
lean_dec(v_i_1197_);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v_a_1198_);
return v___x_1208_;
}
else
{
lean_object* v_one_1209_; lean_object* v_n_1210_; lean_object* v___y_1212_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v_one_1209_ = lean_unsigned_to_nat(1u);
v_n_1210_ = lean_nat_sub(v_i_1197_, v_one_1209_);
lean_dec(v_i_1197_);
v___x_1215_ = lean_array_fget_borrowed(v_xs_1196_, v_n_1210_);
v___x_1216_ = l_Lean_Expr_fvarId_x21(v___x_1215_);
v___x_1217_ = l_Lean_FVarId_getDecl___redArg(v___x_1216_, v___y_1201_, v___y_1203_, v___y_1204_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v_a_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; lean_object* v___x_1224_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1217_, 1);
v___x_1219_ = l_Lean_LocalDecl_type(v_a_1218_);
v___x_1220_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v___x_1219_, v_n_1210_, v_xs_1196_, v___y_1200_, v___y_1201_);
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref(v___x_1220_);
v___x_1222_ = l_Lean_LocalDecl_userName(v_a_1218_);
v___x_1223_ = l_Lean_LocalDecl_binderInfo(v_a_1218_);
lean_dec(v_a_1218_);
v___x_1224_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v___x_1222_, v___x_1223_, v_a_1221_, v_a_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
v___y_1212_ = v___x_1224_;
goto v___jp_1211_;
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec(v_n_1210_);
lean_dec_ref(v_a_1198_);
v_a_1225_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1217_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1217_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
v___jp_1211_:
{
if (lean_obj_tag(v___y_1212_) == 0)
{
lean_object* v_a_1213_; 
v_a_1213_ = lean_ctor_get(v___y_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___y_1212_, 1);
v_i_1197_ = v_n_1210_;
v_a_1198_ = v_a_1213_;
goto _start;
}
else
{
lean_dec(v_n_1210_);
return v___y_1212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg___boxed(lean_object* v_xs_1233_, lean_object* v_i_1234_, lean_object* v_a_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1233_, v_i_1234_, v_a_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec_ref(v_xs_1233_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS(lean_object* v_xs_1244_, lean_object* v_e_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v_a_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1253_ = lean_unsigned_to_nat(0u);
v___x_1254_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v_e_1245_, v___x_1253_, v_xs_1244_, v_a_1247_, v_a_1248_);
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref(v___x_1254_);
v___x_1256_ = lean_array_get_size(v_xs_1244_);
v___x_1257_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1244_, v___x_1256_, v_a_1255_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS___boxed(lean_object* v_xs_1258_, lean_object* v_e_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_1258_, v_e_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec_ref(v_xs_1258_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(lean_object* v_xs_1268_, lean_object* v_n_1269_, lean_object* v_i_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1268_, v_i_1270_, v_a_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___boxed(lean_object* v_xs_1281_, lean_object* v_n_1282_, lean_object* v_i_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(v_xs_1281_, v_n_1282_, v_i_1283_, v_a_1284_, v_a_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v_n_1282_);
lean_dec_ref(v_xs_1281_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(lean_object* v_x_1294_, uint8_t v_bi_1295_, lean_object* v_t_1296_, lean_object* v_b_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___y_1306_; lean_object* v___x_1309_; uint8_t v_debug_1310_; 
v___x_1309_ = lean_st_ref_get(v___y_1299_);
v_debug_1310_ = lean_ctor_get_uint8(v___x_1309_, sizeof(void*)*10);
lean_dec(v___x_1309_);
if (v_debug_1310_ == 0)
{
v___y_1306_ = v___y_1299_;
goto v___jp_1305_;
}
else
{
lean_object* v___x_1311_; 
lean_inc_ref(v_t_1296_);
v___x_1311_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1296_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v___x_1312_; 
lean_dec_ref_known(v___x_1311_, 1);
lean_inc_ref(v_b_1297_);
v___x_1312_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_dec_ref_known(v___x_1312_, 1);
v___y_1306_ = v___y_1299_;
goto v___jp_1305_;
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec_ref(v_b_1297_);
lean_dec_ref(v_t_1296_);
lean_dec(v_x_1294_);
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1312_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
lean_dec_ref(v_b_1297_);
lean_dec_ref(v_t_1296_);
lean_dec(v_x_1294_);
v_a_1321_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1323_ = v___x_1311_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1311_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1321_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
v___jp_1305_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = l_Lean_Expr_forallE___override(v_x_1294_, v_t_1296_, v_b_1297_, v_bi_1295_);
v___x_1308_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1307_, v___y_1306_);
return v___x_1308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0___boxed(lean_object* v_x_1329_, lean_object* v_bi_1330_, lean_object* v_t_1331_, lean_object* v_b_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
uint8_t v_bi_boxed_1340_; lean_object* v_res_1341_; 
v_bi_boxed_1340_ = lean_unbox(v_bi_1330_);
v_res_1341_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v_x_1329_, v_bi_boxed_1340_, v_t_1331_, v_b_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(lean_object* v_xs_1342_, lean_object* v_i_1343_, lean_object* v_a_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_zero_1352_; uint8_t v_isZero_1353_; 
v_zero_1352_ = lean_unsigned_to_nat(0u);
v_isZero_1353_ = lean_nat_dec_eq(v_i_1343_, v_zero_1352_);
if (v_isZero_1353_ == 1)
{
lean_object* v___x_1354_; 
lean_dec(v_i_1343_);
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v_a_1344_);
return v___x_1354_;
}
else
{
lean_object* v_one_1355_; lean_object* v_n_1356_; lean_object* v___y_1358_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v_one_1355_ = lean_unsigned_to_nat(1u);
v_n_1356_ = lean_nat_sub(v_i_1343_, v_one_1355_);
lean_dec(v_i_1343_);
v___x_1361_ = lean_array_fget_borrowed(v_xs_1342_, v_n_1356_);
v___x_1362_ = l_Lean_Expr_fvarId_x21(v___x_1361_);
v___x_1363_ = l_Lean_FVarId_getDecl___redArg(v___x_1362_, v___y_1347_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v_a_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; lean_object* v___x_1370_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v___x_1363_, 1);
v___x_1365_ = l_Lean_LocalDecl_type(v_a_1364_);
v___x_1366_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v___x_1365_, v_n_1356_, v_xs_1342_, v___y_1346_, v___y_1347_);
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref(v___x_1366_);
v___x_1368_ = l_Lean_LocalDecl_userName(v_a_1364_);
v___x_1369_ = l_Lean_LocalDecl_binderInfo(v_a_1364_);
lean_dec(v_a_1364_);
v___x_1370_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v___x_1368_, v___x_1369_, v_a_1367_, v_a_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
v___y_1358_ = v___x_1370_;
goto v___jp_1357_;
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec(v_n_1356_);
lean_dec_ref(v_a_1344_);
v_a_1371_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1363_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1363_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
v___jp_1357_:
{
if (lean_obj_tag(v___y_1358_) == 0)
{
lean_object* v_a_1359_; 
v_a_1359_ = lean_ctor_get(v___y_1358_, 0);
lean_inc(v_a_1359_);
lean_dec_ref_known(v___y_1358_, 1);
v_i_1343_ = v_n_1356_;
v_a_1344_ = v_a_1359_;
goto _start;
}
else
{
lean_dec(v_n_1356_);
return v___y_1358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg___boxed(lean_object* v_xs_1379_, lean_object* v_i_1380_, lean_object* v_a_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1379_, v_i_1380_, v_a_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec_ref(v_xs_1379_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS(lean_object* v_xs_1390_, lean_object* v_e_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v_a_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1400_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v_e_1391_, v___x_1399_, v_xs_1390_, v_a_1393_, v_a_1394_);
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref(v___x_1400_);
v___x_1402_ = lean_array_get_size(v_xs_1390_);
v___x_1403_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1390_, v___x_1402_, v_a_1401_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS___boxed(lean_object* v_xs_1404_, lean_object* v_e_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_Meta_Sym_mkForallFVarsS(v_xs_1404_, v_e_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec_ref(v_xs_1404_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(lean_object* v_xs_1414_, lean_object* v_n_1415_, lean_object* v_i_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1414_, v_i_1416_, v_a_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___boxed(lean_object* v_xs_1427_, lean_object* v_n_1428_, lean_object* v_i_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(v_xs_1427_, v_n_1428_, v_i_1429_, v_a_1430_, v_a_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v_n_1428_);
lean_dec_ref(v_xs_1427_);
return v_res_1439_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_ReplaceS(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_ReplaceS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_AbstractS(builtin);
}
#ifdef __cplusplus
}
#endif
