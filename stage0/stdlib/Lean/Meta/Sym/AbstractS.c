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
size_t lean_usize_shift_left(size_t, size_t);
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
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1;
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
lean_dec_ref(v_e_18_);
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
lean_dec_ref(v___x_76_);
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
lean_dec_ref(v_val_77_);
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
lean_dec_ref(v___x_32_);
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
lean_dec_ref(v___x_196_);
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
lean_dec_ref(v_fst_117_);
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
uint8_t v___y_25263__boxed_263_; lean_object* v_res_264_; 
v___y_25263__boxed_263_ = lean_unbox(v___y_261_);
v_res_264_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(v_idx_260_, v___y_25263__boxed_263_, v___y_262_);
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
uint8_t v___y_25276__boxed_297_; lean_object* v_res_298_; 
v___y_25276__boxed_297_ = lean_unbox(v___y_295_);
v_res_298_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__12(v_structName_291_, v_idx_292_, v_struct_293_, v___y_294_, v___y_25276__boxed_297_, v___y_296_);
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
uint8_t v___y_25320__boxed_326_; lean_object* v_res_327_; 
v___y_25320__boxed_326_ = lean_unbox(v___y_324_);
v_res_327_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__11(v_d_321_, v_e_322_, v___y_323_, v___y_25320__boxed_326_, v___y_325_);
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
uint8_t v_bi_boxed_361_; uint8_t v___y_25364__boxed_362_; lean_object* v_res_363_; 
v_bi_boxed_361_ = lean_unbox(v_bi_355_);
v___y_25364__boxed_362_ = lean_unbox(v___y_359_);
v_res_363_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__9(v_x_354_, v_bi_boxed_361_, v_t_356_, v_b_357_, v___y_358_, v___y_25364__boxed_362_, v___y_360_);
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
uint8_t v_bi_boxed_397_; uint8_t v___y_25413__boxed_398_; lean_object* v_res_399_; 
v_bi_boxed_397_ = lean_unbox(v_bi_391_);
v___y_25413__boxed_398_ = lean_unbox(v___y_395_);
v_res_399_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__8(v_x_390_, v_bi_boxed_397_, v_t_392_, v_b_393_, v___y_394_, v___y_25413__boxed_398_, v___y_396_);
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
uint8_t v_nondep_boxed_437_; uint8_t v___y_25462__boxed_438_; lean_object* v_res_439_; 
v_nondep_boxed_437_ = lean_unbox(v_nondep_433_);
v___y_25462__boxed_438_ = lean_unbox(v___y_435_);
v_res_439_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10(v_x_429_, v_t_430_, v_v_431_, v_b_432_, v_nondep_boxed_437_, v___y_434_, v___y_25462__boxed_438_, v___y_436_);
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
uint8_t v___y_25516__boxed_469_; lean_object* v_res_470_; 
v___y_25516__boxed_469_ = lean_unbox(v___y_467_);
v_res_470_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__7(v_f_464_, v_a_465_, v___y_466_, v___y_25516__boxed_469_, v___y_468_);
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
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_534_; size_t v___x_535_; size_t v___x_536_; 
v___x_534_ = ((size_t)5ULL);
v___x_535_ = ((size_t)1ULL);
v___x_536_ = lean_usize_shift_left(v___x_535_, v___x_534_);
return v___x_536_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_537_; size_t v___x_538_; size_t v___x_539_; 
v___x_537_ = ((size_t)1ULL);
v___x_538_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__0);
v___x_539_ = lean_usize_sub(v___x_538_, v___x_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(lean_object* v_x_540_, size_t v_x_541_, lean_object* v_x_542_){
_start:
{
if (lean_obj_tag(v_x_540_) == 0)
{
lean_object* v_es_543_; lean_object* v___x_544_; size_t v___x_545_; size_t v___x_546_; size_t v___x_547_; lean_object* v_j_548_; lean_object* v___x_549_; 
v_es_543_ = lean_ctor_get(v_x_540_, 0);
v___x_544_ = lean_box(2);
v___x_545_ = ((size_t)5ULL);
v___x_546_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1);
v___x_547_ = lean_usize_land(v_x_541_, v___x_546_);
v_j_548_ = lean_usize_to_nat(v___x_547_);
v___x_549_ = lean_array_get_borrowed(v___x_544_, v_es_543_, v_j_548_);
lean_dec(v_j_548_);
switch(lean_obj_tag(v___x_549_))
{
case 0:
{
lean_object* v_key_550_; lean_object* v_val_551_; uint8_t v___x_552_; 
v_key_550_ = lean_ctor_get(v___x_549_, 0);
v_val_551_ = lean_ctor_get(v___x_549_, 1);
v___x_552_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_542_, v_key_550_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; 
v___x_553_ = lean_box(0);
return v___x_553_;
}
else
{
lean_object* v___x_554_; 
lean_inc(v_val_551_);
v___x_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_554_, 0, v_val_551_);
return v___x_554_;
}
}
case 1:
{
lean_object* v_node_555_; size_t v___x_556_; 
v_node_555_ = lean_ctor_get(v___x_549_, 0);
v___x_556_ = lean_usize_shift_right(v_x_541_, v___x_545_);
v_x_540_ = v_node_555_;
v_x_541_ = v___x_556_;
goto _start;
}
default: 
{
lean_object* v___x_558_; 
v___x_558_ = lean_box(0);
return v___x_558_;
}
}
}
else
{
lean_object* v_ks_559_; lean_object* v_vs_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_ks_559_ = lean_ctor_get(v_x_540_, 0);
v_vs_560_ = lean_ctor_get(v_x_540_, 1);
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg(v_ks_559_, v_vs_560_, v___x_561_, v_x_542_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___boxed(lean_object* v_x_563_, lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
size_t v_x_25664__boxed_566_; lean_object* v_res_567_; 
v_x_25664__boxed_566_ = lean_unbox_usize(v_x_564_);
lean_dec(v_x_564_);
v_res_567_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(v_x_563_, v_x_25664__boxed_566_, v_x_565_);
lean_dec_ref(v_x_565_);
lean_dec_ref(v_x_563_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
uint64_t v___x_570_; size_t v___x_571_; lean_object* v___x_572_; 
v___x_570_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_569_);
v___x_571_ = lean_uint64_to_usize(v___x_570_);
v___x_572_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(v_x_568_, v___x_571_, v_x_569_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg___boxed(lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(v_x_573_, v_x_574_);
lean_dec_ref(v_x_574_);
lean_dec_ref(v_x_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13(lean_object* v_msg_583_, lean_object* v___y_584_, uint8_t v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v___f_587_; lean_object* v___f_588_; lean_object* v___f_589_; lean_object* v___f_590_; lean_object* v___f_591_; lean_object* v___f_592_; lean_object* v___f_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___f_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___f_608_; lean_object* v___f_609_; lean_object* v___f_610_; lean_object* v___f_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_24871__overap_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___f_587_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__0));
v___f_588_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__1));
v___f_589_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__2));
v___f_590_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__3));
v___f_591_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__4));
v___f_592_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__5));
v___f_593_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__6));
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v___f_587_);
lean_ctor_set(v___x_594_, 1, v___f_588_);
v___x_595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___f_589_);
lean_ctor_set(v___x_595_, 2, v___f_590_);
lean_ctor_set(v___x_595_, 3, v___f_591_);
lean_ctor_set(v___x_595_, 4, v___f_592_);
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v___f_593_);
lean_inc_ref_n(v___x_596_, 6);
v___f_597_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_597_, 0, v___x_596_);
v___f_598_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_598_, 0, v___x_596_);
v___f_599_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_599_, 0, v___x_596_);
v___f_600_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_600_, 0, v___x_596_);
v___x_601_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_601_, 0, lean_box(0));
lean_closure_set(v___x_601_, 1, lean_box(0));
lean_closure_set(v___x_601_, 2, v___x_596_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___f_597_);
v___x_603_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_603_, 0, lean_box(0));
lean_closure_set(v___x_603_, 1, lean_box(0));
lean_closure_set(v___x_603_, 2, v___x_596_);
v___x_604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_604_, 0, v___x_602_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
lean_ctor_set(v___x_604_, 2, v___f_598_);
lean_ctor_set(v___x_604_, 3, v___f_599_);
lean_ctor_set(v___x_604_, 4, v___f_600_);
v___x_605_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_605_, 0, lean_box(0));
lean_closure_set(v___x_605_, 1, lean_box(0));
lean_closure_set(v___x_605_, 2, v___x_596_);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = l_ReaderT_instMonad___redArg(v___x_606_);
lean_inc_ref_n(v___x_607_, 6);
v___f_608_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_608_, 0, v___x_607_);
v___f_609_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_609_, 0, v___x_607_);
v___f_610_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_610_, 0, v___x_607_);
v___f_611_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_611_, 0, v___x_607_);
v___x_612_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_612_, 0, lean_box(0));
lean_closure_set(v___x_612_, 1, lean_box(0));
lean_closure_set(v___x_612_, 2, v___x_607_);
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___f_608_);
v___x_614_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_614_, 0, lean_box(0));
lean_closure_set(v___x_614_, 1, lean_box(0));
lean_closure_set(v___x_614_, 2, v___x_607_);
v___x_615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
lean_ctor_set(v___x_615_, 2, v___f_609_);
lean_ctor_set(v___x_615_, 3, v___f_610_);
lean_ctor_set(v___x_615_, 4, v___f_611_);
v___x_616_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_616_, 0, lean_box(0));
lean_closure_set(v___x_616_, 1, lean_box(0));
lean_closure_set(v___x_616_, 2, v___x_607_);
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = l_Lean_instInhabitedExpr;
v___x_619_ = l_instInhabitedOfMonad___redArg(v___x_617_, v___x_618_);
v___x_24871__overap_620_ = lean_panic_fn_borrowed(v___x_619_, v_msg_583_);
lean_dec(v___x_619_);
v___x_621_ = lean_box(v___y_585_);
v___x_622_ = lean_apply_3(v___x_24871__overap_620_, v___y_584_, v___x_621_, v___y_586_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___boxed(lean_object* v_msg_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
uint8_t v___y_25743__boxed_627_; lean_object* v_res_628_; 
v___y_25743__boxed_627_ = lean_unbox(v___y_625_);
v_res_628_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13(v_msg_623_, v___y_624_, v___y_25743__boxed_627_, v___y_626_);
return v_res_628_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_632_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__2));
v___x_633_ = lean_unsigned_to_nat(67u);
v___x_634_ = lean_unsigned_to_nat(35u);
v___x_635_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__1));
v___x_636_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0));
v___x_637_ = l_mkPanicMessageWithDecl(v___x_636_, v___x_635_, v___x_634_, v___x_633_, v___x_632_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(lean_object* v_minIndex_638_, lean_object* v___x_639_, lean_object* v___x_640_, lean_object* v_start_641_, lean_object* v_xs_642_, lean_object* v___x_643_, lean_object* v_e_644_, lean_object* v_offset_645_, lean_object* v_a_646_, uint8_t v_a_647_, lean_object* v_a_648_){
_start:
{
switch(lean_obj_tag(v_e_644_))
{
case 5:
{
lean_object* v_fn_649_; lean_object* v_arg_650_; lean_object* v___x_651_; lean_object* v_fst_652_; lean_object* v_snd_653_; lean_object* v_fst_654_; lean_object* v_snd_655_; lean_object* v___x_656_; lean_object* v_fst_657_; lean_object* v_snd_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_679_; 
v_fn_649_ = lean_ctor_get(v_e_644_, 0);
v_arg_650_ = lean_ctor_get(v_e_644_, 1);
lean_inc(v_offset_645_);
lean_inc_ref(v_fn_649_);
lean_inc_ref(v___x_639_);
v___x_651_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_638_, v___x_639_, v___x_640_, v_start_641_, v_xs_642_, v___x_643_, v_fn_649_, v_offset_645_, v_a_646_, v_a_647_, v_a_648_);
v_fst_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_fst_652_);
v_snd_653_ = lean_ctor_get(v___x_651_, 1);
lean_inc(v_snd_653_);
lean_dec_ref(v___x_651_);
v_fst_654_ = lean_ctor_get(v_fst_652_, 0);
lean_inc(v_fst_654_);
v_snd_655_ = lean_ctor_get(v_fst_652_, 1);
lean_inc(v_snd_655_);
lean_dec(v_fst_652_);
lean_inc_ref(v_arg_650_);
v___x_656_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_638_, v___x_639_, v___x_640_, v_start_641_, v_xs_642_, v___x_643_, v_arg_650_, v_offset_645_, v_snd_655_, v_a_647_, v_snd_653_);
v_fst_657_ = lean_ctor_get(v___x_656_, 0);
v_snd_658_ = lean_ctor_get(v___x_656_, 1);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_679_ == 0)
{
v___x_660_ = v___x_656_;
v_isShared_661_ = v_isSharedCheck_679_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_snd_658_);
lean_inc(v_fst_657_);
lean_dec(v___x_656_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_679_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v_fst_662_; lean_object* v_snd_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_678_; 
v_fst_662_ = lean_ctor_get(v_fst_657_, 0);
v_snd_663_ = lean_ctor_get(v_fst_657_, 1);
v_isSharedCheck_678_ = !lean_is_exclusive(v_fst_657_);
if (v_isSharedCheck_678_ == 0)
{
v___x_665_ = v_fst_657_;
v_isShared_666_ = v_isSharedCheck_678_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_snd_663_);
lean_inc(v_fst_662_);
lean_dec(v_fst_657_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_678_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
uint8_t v___y_668_; uint8_t v___x_676_; 
v___x_676_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_649_, v_fst_654_);
if (v___x_676_ == 0)
{
v___y_668_ = v___x_676_;
goto v___jp_667_;
}
else
{
uint8_t v___x_677_; 
v___x_677_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_650_, v_fst_662_);
v___y_668_ = v___x_677_;
goto v___jp_667_;
}
v___jp_667_:
{
if (v___y_668_ == 0)
{
lean_object* v___x_669_; 
lean_del_object(v___x_665_);
lean_del_object(v___x_660_);
lean_dec_ref(v_e_644_);
v___x_669_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__7(v_fst_654_, v_fst_662_, v_snd_663_, v_a_647_, v_snd_658_);
return v___x_669_;
}
else
{
lean_object* v___x_671_; 
lean_dec(v_fst_662_);
lean_dec(v_fst_654_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v_e_644_);
v___x_671_ = v___x_665_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_e_644_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_snd_663_);
v___x_671_ = v_reuseFailAlloc_675_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_673_; 
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_671_);
v___x_673_ = v___x_660_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_snd_658_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
}
}
case 6:
{
lean_object* v_binderName_680_; lean_object* v_binderType_681_; lean_object* v_body_682_; uint8_t v_binderInfo_683_; lean_object* v___x_684_; lean_object* v_fst_685_; lean_object* v_snd_686_; lean_object* v_fst_687_; lean_object* v_snd_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v_fst_692_; lean_object* v_snd_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_714_; 
v_binderName_680_ = lean_ctor_get(v_e_644_, 0);
v_binderType_681_ = lean_ctor_get(v_e_644_, 1);
v_body_682_ = lean_ctor_get(v_e_644_, 2);
v_binderInfo_683_ = lean_ctor_get_uint8(v_e_644_, sizeof(void*)*3 + 8);
lean_inc(v_offset_645_);
lean_inc_ref(v_binderType_681_);
lean_inc_ref(v___x_639_);
v___x_684_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_638_, v___x_639_, v___x_640_, v_start_641_, v_xs_642_, v___x_643_, v_binderType_681_, v_offset_645_, v_a_646_, v_a_647_, v_a_648_);
v_fst_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_fst_685_);
v_snd_686_ = lean_ctor_get(v___x_684_, 1);
lean_inc(v_snd_686_);
lean_dec_ref(v___x_684_);
v_fst_687_ = lean_ctor_get(v_fst_685_, 0);
lean_inc(v_fst_687_);
v_snd_688_ = lean_ctor_get(v_fst_685_, 1);
lean_inc(v_snd_688_);
lean_dec(v_fst_685_);
v___x_689_ = lean_unsigned_to_nat(1u);
v___x_690_ = lean_nat_add(v_offset_645_, v___x_689_);
lean_dec(v_offset_645_);
lean_inc_ref(v_body_682_);
v___x_691_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_638_, v___x_639_, v___x_640_, v_start_641_, v_xs_642_, v___x_643_, v_body_682_, v___x_690_, v_snd_688_, v_a_647_, v_snd_686_);
v_fst_692_ = lean_ctor_get(v___x_691_, 0);
v_snd_693_ = lean_ctor_get(v___x_691_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_714_ == 0)
{
v___x_695_ = v___x_691_;
v_isShared_696_ = v_isSharedCheck_714_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_snd_693_);
lean_inc(v_fst_692_);
lean_dec(v___x_691_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_714_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_fst_697_; lean_object* v_snd_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_713_; 
v_fst_697_ = lean_ctor_get(v_fst_692_, 0);
v_snd_698_ = lean_ctor_get(v_fst_692_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v_fst_692_);
if (v_isSharedCheck_713_ == 0)
{
v___x_700_ = v_fst_692_;
v_isShared_701_ = v_isSharedCheck_713_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_snd_698_);
lean_inc(v_fst_697_);
lean_dec(v_fst_692_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_713_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
uint8_t v___y_703_; uint8_t v___x_711_; 
v___x_711_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_681_, v_fst_687_);
if (v___x_711_ == 0)
{
v___y_703_ = v___x_711_;
goto v___jp_702_;
}
else
{
uint8_t v___x_712_; 
v___x_712_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_682_, v_fst_697_);
v___y_703_ = v___x_712_;
goto v___jp_702_;
}
v___jp_702_:
{
if (v___y_703_ == 0)
{
lean_object* v___x_704_; 
lean_inc(v_binderName_680_);
lean_del_object(v___x_700_);
lean_del_object(v___x_695_);
lean_dec_ref(v_e_644_);
v___x_704_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__8(v_binderName_680_, v_binderInfo_683_, v_fst_687_, v_fst_697_, v_snd_698_, v_a_647_, v_snd_693_);
return v___x_704_;
}
else
{
lean_object* v___x_706_; 
lean_dec(v_fst_697_);
lean_dec(v_fst_687_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v_e_644_);
v___x_706_ = v___x_700_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_e_644_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_snd_698_);
v___x_706_ = v_reuseFailAlloc_710_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_708_; 
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_706_);
v___x_708_ = v___x_695_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_snd_693_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_715_; lean_object* v_binderType_716_; lean_object* v_body_717_; uint8_t v_binderInfo_718_; lean_object* v___x_719_; lean_object* v_fst_720_; lean_object* v_snd_721_; lean_object* v_fst_722_; lean_object* v_snd_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v_fst_727_; lean_object* v_snd_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_749_; 
v_binderName_715_ = lean_ctor_get(v_e_644_, 0);
v_binderType_716_ = lean_ctor_get(v_e_644_, 1);
v_body_717_ = lean_ctor_get(v_e_644_, 2);
v_binderInfo_718_ = lean_ctor_get_uint8(v_e_644_, sizeof(void*)*3 + 8);
lean_inc(v_offset_645_);
lean_inc_ref(v_binderType_716_);
lean_inc_ref(v___x_639_);
v___x_719_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_638_, v___x_639_, v___x_640_, v_start_641_, v_xs_642_, v___x_643_, v_binderType_716_, v_offset_645_, v_a_646_, v_a_647_, v_a_648_);
v_fst_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_fst_720_);
v_snd_721_ = lean_ctor_get(v___x_719_, 1);
lean_inc(v_snd_721_);
lean_dec_ref(v___x_719_);
v_fst_722_ = lean_ctor_get(v_fst_720_, 0);
lean_inc(v_fst_722_);
v_snd_723_ = lean_ctor_get(v_fst_720_, 1);
lean_inc(v_snd_723_);
lean_dec(v_fst_720_);
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_nat_add(v_offset_645_, v___x_724_);
lean_dec(v_offset_645_);
lean_inc_ref(v_body_717_);
v___x_726_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_638_, v___x_639_, v___x_640_, v_start_641_, v_xs_642_, v___x_643_, v_body_717_, v___x_725_, v_snd_723_, v_a_647_, v_snd_721_);
v_fst_727_ = lean_ctor_get(v___x_726_, 0);
v_snd_728_ = lean_ctor_get(v___x_726_, 1);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_749_ == 0)
{
v___x_730_ = v___x_726_;
v_isShared_731_ = v_isSharedCheck_749_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_snd_728_);
lean_inc(v_fst_727_);
lean_dec(v___x_726_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_749_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v_fst_732_; lean_object* v_snd_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_748_; 
v_fst_732_ = lean_ctor_get(v_fst_727_, 0);
v_snd_733_ = lean_ctor_get(v_fst_727_, 1);
v_isSharedCheck_748_ = !lean_is_exclusive(v_fst_727_);
if (v_isSharedCheck_748_ == 0)
{
v___x_735_ = v_fst_727_;
v_isShared_736_ = v_isSharedCheck_748_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_snd_733_);
lean_inc(v_fst_732_);
lean_dec(v_fst_727_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_748_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
uint8_t v___y_738_; uint8_t v___x_746_; 
v___x_746_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_716_, v_fst_722_);
if (v___x_746_ == 0)
{
v___y_738_ = v___x_746_;
goto v___jp_737_;
}
else
{
uint8_t v___x_747_; 
v___x_747_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_717_, v_fst_732_);
v___y_738_ = v___x_747_;
goto v___jp_737_;
}
v___jp_737_:
{
if (v___y_738_ == 0)
{
lean_object* v___x_739_; 
lean_inc(v_binderName_715_);
lean_del_object(v___x_735_);
lean_del_object(v___x_730_);
lean_dec_ref(v_e_644_);
v___x_739_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__9(v_binderName_715_, v_binderInfo_718_, v_fst_722_, v_fst_732_, v_snd_733_, v_a_647_, v_snd_728_);
return v___x_739_;
}
else
{
lean_object* v___x_741_; 
lean_dec(v_fst_732_);
lean_dec(v_fst_722_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v_e_644_);
v___x_741_ = v___x_735_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_e_644_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_snd_733_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_741_);
v___x_743_ = v___x_730_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_snd_728_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_750_; lean_object* v_type_751_; lean_object* v_value_752_; lean_object* v_body_753_; uint8_t v_nondep_754_; lean_object* v___x_755_; lean_object* v_fst_756_; lean_object* v_snd_757_; lean_object* v_fst_758_; lean_object* v_snd_759_; lean_object* v___x_760_; lean_object* v_fst_761_; lean_object* v_snd_762_; lean_object* v_fst_763_; lean_object* v_snd_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v_fst_768_; lean_object* v_snd_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_792_; 
v_declName_750_ = lean_ctor_get(v_e_644_, 0);
v_type_751_ = lean_ctor_get(v_e_644_, 1);
v_value_752_ = lean_ctor_get(v_e_644_, 2);
v_body_753_ = lean_ctor_get(v_e_644_, 3);
v_nondep_754_ = lean_ctor_get_uint8(v_e_644_, sizeof(void*)*4 + 8);
lean_inc_n(v_offset_645_, 2);
lean_inc_ref(v_type_751_);
lean_inc_ref_n(v___x_639_, 2);
v___x_755_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_638_, v___x_639_, v___x_640_, v_start_641_, v_xs_642_, v___x_643_, v_type_751_, v_offset_645_, v_a_646_, v_a_647_, v_a_648_);
v_fst_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_fst_756_);
v_snd_757_ = lean_ctor_get(v___x_755_, 1);
lean_inc(v_snd_757_);
lean_dec_ref(v___x_755_);
v_fst_758_ = lean_ctor_get(v_fst_756_, 0);
lean_inc(v_fst_758_);
v_snd_759_ = lean_ctor_get(v_fst_756_, 1);
lean_inc(v_snd_759_);
lean_dec(v_fst_756_);
lean_inc_ref(v_value_752_);
v___x_760_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_638_, v___x_639_, v___x_640_, v_start_641_, v_xs_642_, v___x_643_, v_value_752_, v_offset_645_, v_snd_759_, v_a_647_, v_snd_757_);
v_fst_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_fst_761_);
v_snd_762_ = lean_ctor_get(v___x_760_, 1);
lean_inc(v_snd_762_);
lean_dec_ref(v___x_760_);
v_fst_763_ = lean_ctor_get(v_fst_761_, 0);
lean_inc(v_fst_763_);
v_snd_764_ = lean_ctor_get(v_fst_761_, 1);
lean_inc(v_snd_764_);
lean_dec(v_fst_761_);
v___x_765_ = lean_unsigned_to_nat(1u);
v___x_766_ = lean_nat_add(v_offset_645_, v___x_765_);
lean_dec(v_offset_645_);
lean_inc_ref(v_body_753_);
v___x_767_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_638_, v___x_639_, v___x_640_, v_start_641_, v_xs_642_, v___x_643_, v_body_753_, v___x_766_, v_snd_764_, v_a_647_, v_snd_762_);
v_fst_768_ = lean_ctor_get(v___x_767_, 0);
v_snd_769_ = lean_ctor_get(v___x_767_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_792_ == 0)
{
v___x_771_ = v___x_767_;
v_isShared_772_ = v_isSharedCheck_792_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_snd_769_);
lean_inc(v_fst_768_);
lean_dec(v___x_767_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_792_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v_fst_773_; lean_object* v_snd_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_791_; 
v_fst_773_ = lean_ctor_get(v_fst_768_, 0);
v_snd_774_ = lean_ctor_get(v_fst_768_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v_fst_768_);
if (v_isSharedCheck_791_ == 0)
{
v___x_776_ = v_fst_768_;
v_isShared_777_ = v_isSharedCheck_791_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_snd_774_);
lean_inc(v_fst_773_);
lean_dec(v_fst_768_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_791_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
uint8_t v___y_779_; uint8_t v___x_789_; 
v___x_789_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_751_, v_fst_758_);
if (v___x_789_ == 0)
{
v___y_779_ = v___x_789_;
goto v___jp_778_;
}
else
{
uint8_t v___x_790_; 
v___x_790_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_752_, v_fst_763_);
v___y_779_ = v___x_790_;
goto v___jp_778_;
}
v___jp_778_:
{
if (v___y_779_ == 0)
{
lean_object* v___x_780_; 
lean_inc(v_declName_750_);
lean_del_object(v___x_776_);
lean_del_object(v___x_771_);
lean_dec_ref(v_e_644_);
v___x_780_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10(v_declName_750_, v_fst_758_, v_fst_763_, v_fst_773_, v_nondep_754_, v_snd_774_, v_a_647_, v_snd_769_);
return v___x_780_;
}
else
{
uint8_t v___x_781_; 
v___x_781_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_753_, v_fst_773_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; 
lean_inc(v_declName_750_);
lean_del_object(v___x_776_);
lean_del_object(v___x_771_);
lean_dec_ref(v_e_644_);
v___x_782_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10(v_declName_750_, v_fst_758_, v_fst_763_, v_fst_773_, v_nondep_754_, v_snd_774_, v_a_647_, v_snd_769_);
return v___x_782_;
}
else
{
lean_object* v___x_784_; 
lean_dec(v_fst_773_);
lean_dec(v_fst_763_);
lean_dec(v_fst_758_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v_e_644_);
v___x_784_ = v___x_776_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_e_644_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_snd_774_);
v___x_784_ = v_reuseFailAlloc_788_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_786_; 
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_784_);
v___x_786_ = v___x_771_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_snd_769_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
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
lean_object* v_data_793_; lean_object* v_expr_794_; lean_object* v___x_795_; lean_object* v_fst_796_; lean_object* v_snd_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_815_; 
v_data_793_ = lean_ctor_get(v_e_644_, 0);
v_expr_794_ = lean_ctor_get(v_e_644_, 1);
lean_inc_ref(v_expr_794_);
v___x_795_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_638_, v___x_639_, v___x_640_, v_start_641_, v_xs_642_, v___x_643_, v_expr_794_, v_offset_645_, v_a_646_, v_a_647_, v_a_648_);
v_fst_796_ = lean_ctor_get(v___x_795_, 0);
v_snd_797_ = lean_ctor_get(v___x_795_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_815_ == 0)
{
v___x_799_ = v___x_795_;
v_isShared_800_ = v_isSharedCheck_815_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_snd_797_);
lean_inc(v_fst_796_);
lean_dec(v___x_795_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_815_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_fst_801_; lean_object* v_snd_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_814_; 
v_fst_801_ = lean_ctor_get(v_fst_796_, 0);
v_snd_802_ = lean_ctor_get(v_fst_796_, 1);
v_isSharedCheck_814_ = !lean_is_exclusive(v_fst_796_);
if (v_isSharedCheck_814_ == 0)
{
v___x_804_ = v_fst_796_;
v_isShared_805_ = v_isSharedCheck_814_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_snd_802_);
lean_inc(v_fst_801_);
lean_dec(v_fst_796_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_814_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
uint8_t v___x_806_; 
v___x_806_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_794_, v_fst_801_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; 
lean_inc(v_data_793_);
lean_del_object(v___x_804_);
lean_del_object(v___x_799_);
lean_dec_ref(v_e_644_);
v___x_807_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__11(v_data_793_, v_fst_801_, v_snd_802_, v_a_647_, v_snd_797_);
return v___x_807_;
}
else
{
lean_object* v___x_809_; 
lean_dec(v_fst_801_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v_e_644_);
v___x_809_ = v___x_804_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_e_644_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_snd_802_);
v___x_809_ = v_reuseFailAlloc_813_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_811_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_809_);
v___x_811_ = v___x_799_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_snd_797_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_816_; lean_object* v_idx_817_; lean_object* v_struct_818_; lean_object* v___x_819_; lean_object* v_fst_820_; lean_object* v_snd_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_839_; 
v_typeName_816_ = lean_ctor_get(v_e_644_, 0);
v_idx_817_ = lean_ctor_get(v_e_644_, 1);
v_struct_818_ = lean_ctor_get(v_e_644_, 2);
lean_inc_ref(v_struct_818_);
v___x_819_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_638_, v___x_639_, v___x_640_, v_start_641_, v_xs_642_, v___x_643_, v_struct_818_, v_offset_645_, v_a_646_, v_a_647_, v_a_648_);
v_fst_820_ = lean_ctor_get(v___x_819_, 0);
v_snd_821_ = lean_ctor_get(v___x_819_, 1);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_839_ == 0)
{
v___x_823_ = v___x_819_;
v_isShared_824_ = v_isSharedCheck_839_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_snd_821_);
lean_inc(v_fst_820_);
lean_dec(v___x_819_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_839_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_fst_825_; lean_object* v_snd_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_838_; 
v_fst_825_ = lean_ctor_get(v_fst_820_, 0);
v_snd_826_ = lean_ctor_get(v_fst_820_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v_fst_820_);
if (v_isSharedCheck_838_ == 0)
{
v___x_828_ = v_fst_820_;
v_isShared_829_ = v_isSharedCheck_838_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_snd_826_);
lean_inc(v_fst_825_);
lean_dec(v_fst_820_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_838_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
uint8_t v___x_830_; 
v___x_830_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_818_, v_fst_825_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; 
lean_inc(v_idx_817_);
lean_inc(v_typeName_816_);
lean_del_object(v___x_828_);
lean_del_object(v___x_823_);
lean_dec_ref(v_e_644_);
v___x_831_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__12(v_typeName_816_, v_idx_817_, v_fst_825_, v_snd_826_, v_a_647_, v_snd_821_);
return v___x_831_;
}
else
{
lean_object* v___x_833_; 
lean_dec(v_fst_825_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v_e_644_);
v___x_833_ = v___x_828_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_e_644_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_snd_826_);
v___x_833_ = v_reuseFailAlloc_837_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_835_; 
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_833_);
v___x_835_ = v___x_823_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_snd_821_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_840_; lean_object* v___x_841_; 
lean_dec(v_offset_645_);
lean_dec_ref(v_e_644_);
lean_dec_ref(v___x_639_);
v___x_840_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3);
v___x_841_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13(v___x_840_, v_a_646_, v_a_647_, v_a_648_);
return v___x_841_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(lean_object* v_minIndex_842_, lean_object* v___x_843_, lean_object* v___x_844_, lean_object* v_start_845_, lean_object* v_xs_846_, lean_object* v___x_847_, lean_object* v_e_848_, lean_object* v_offset_849_, lean_object* v_a_850_, uint8_t v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_key_853_; lean_object* v_snd_855_; lean_object* v___y_869_; lean_object* v___y_874_; lean_object* v___x_879_; 
lean_inc(v_offset_849_);
lean_inc_ref(v_e_848_);
v_key_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_853_, 0, v_e_848_);
lean_ctor_set(v_key_853_, 1, v_offset_849_);
v___x_879_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg(v_a_850_, v_key_853_);
if (lean_obj_tag(v___x_879_) == 1)
{
lean_object* v_val_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
lean_dec_ref(v_key_853_);
lean_dec(v_offset_849_);
lean_dec_ref(v_e_848_);
lean_dec_ref(v___x_843_);
v_val_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_val_880_);
lean_dec_ref(v___x_879_);
v___x_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_881_, 0, v_val_880_);
lean_ctor_set(v___x_881_, 1, v_a_850_);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v_a_852_);
return v___x_882_;
}
else
{
lean_dec(v___x_879_);
switch(lean_obj_tag(v_e_848_))
{
case 1:
{
lean_object* v_fvarId_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
lean_dec_ref(v___x_843_);
v_fvarId_883_ = lean_ctor_get(v_e_848_, 0);
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = lean_unsigned_to_nat(1u);
v___x_886_ = lean_nat_sub(v___x_844_, v___x_885_);
v___x_887_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_845_, v_xs_846_, v_fvarId_883_, v___x_884_, v___x_886_);
if (lean_obj_tag(v___x_887_) == 1)
{
lean_object* v_val_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v_fst_891_; lean_object* v_snd_892_; lean_object* v___x_893_; 
lean_dec_ref(v_e_848_);
v_val_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_val_888_);
lean_dec_ref(v___x_887_);
v___x_889_ = lean_nat_add(v_offset_849_, v_val_888_);
lean_dec(v_val_888_);
lean_dec(v_offset_849_);
v___x_890_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v___x_889_, v_a_852_);
v_fst_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_fst_891_);
v_snd_892_ = lean_ctor_get(v___x_890_, 1);
lean_inc(v_snd_892_);
lean_dec_ref(v___x_890_);
v___x_893_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_853_, v_fst_891_, v_a_850_, v_a_851_, v_snd_892_);
return v___x_893_;
}
else
{
lean_object* v___x_894_; 
lean_dec(v___x_887_);
lean_dec(v_offset_849_);
v___x_894_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_853_, v_e_848_, v_a_850_, v_a_851_, v_a_852_);
return v___x_894_;
}
}
case 9:
{
lean_object* v___x_895_; 
lean_dec(v_offset_849_);
lean_dec_ref(v___x_843_);
v___x_895_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_853_, v_e_848_, v_a_850_, v_a_851_, v_a_852_);
return v___x_895_;
}
case 2:
{
lean_object* v___x_896_; 
lean_dec(v_offset_849_);
lean_dec_ref(v___x_843_);
v___x_896_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_853_, v_e_848_, v_a_850_, v_a_851_, v_a_852_);
return v___x_896_;
}
case 0:
{
lean_object* v___x_897_; 
lean_dec(v_offset_849_);
lean_dec_ref(v___x_843_);
v___x_897_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_853_, v_e_848_, v_a_850_, v_a_851_, v_a_852_);
return v___x_897_;
}
case 4:
{
lean_object* v___x_898_; 
lean_dec(v_offset_849_);
lean_dec_ref(v___x_843_);
v___x_898_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_853_, v_e_848_, v_a_850_, v_a_851_, v_a_852_);
return v___x_898_;
}
case 3:
{
lean_object* v___x_899_; 
lean_dec(v_offset_849_);
lean_dec_ref(v___x_843_);
v___x_899_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_853_, v_e_848_, v_a_850_, v_a_851_, v_a_852_);
return v___x_899_;
}
default: 
{
uint8_t v___x_900_; 
v___x_900_ = l_Lean_Expr_hasFVar(v_e_848_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
lean_dec(v_offset_849_);
lean_dec_ref(v___x_843_);
v___x_901_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_853_, v_e_848_, v_a_850_, v_a_851_, v_a_852_);
return v___x_901_;
}
else
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(v___x_847_, v_e_848_);
if (lean_obj_tag(v___x_902_) == 1)
{
lean_object* v_val_903_; 
v_val_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_val_903_);
lean_dec_ref(v___x_902_);
if (lean_obj_tag(v_val_903_) == 0)
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_905_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v___x_904_);
v___y_874_ = v___x_905_;
goto v___jp_873_;
}
else
{
lean_object* v_val_906_; 
v_val_906_ = lean_ctor_get(v_val_903_, 0);
lean_inc(v_val_906_);
lean_dec_ref(v_val_903_);
v___y_874_ = v_val_906_;
goto v___jp_873_;
}
}
else
{
lean_dec(v___x_902_);
v_snd_855_ = v_a_852_;
goto v___jp_854_;
}
}
}
}
}
v___jp_854_:
{
switch(lean_obj_tag(v_e_848_))
{
case 9:
{
lean_object* v___x_856_; 
lean_dec(v_offset_849_);
lean_dec_ref(v___x_843_);
v___x_856_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_853_, v_e_848_, v_a_850_, v_a_851_, v_snd_855_);
return v___x_856_;
}
case 2:
{
lean_object* v___x_857_; 
lean_dec(v_offset_849_);
lean_dec_ref(v___x_843_);
v___x_857_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_853_, v_e_848_, v_a_850_, v_a_851_, v_snd_855_);
return v___x_857_;
}
case 0:
{
lean_object* v___x_858_; 
lean_dec(v_offset_849_);
lean_dec_ref(v___x_843_);
v___x_858_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_853_, v_e_848_, v_a_850_, v_a_851_, v_snd_855_);
return v___x_858_;
}
case 1:
{
lean_object* v___x_859_; 
lean_dec(v_offset_849_);
lean_dec_ref(v___x_843_);
v___x_859_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_853_, v_e_848_, v_a_850_, v_a_851_, v_snd_855_);
return v___x_859_;
}
case 4:
{
lean_object* v___x_860_; 
lean_dec(v_offset_849_);
lean_dec_ref(v___x_843_);
v___x_860_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_853_, v_e_848_, v_a_850_, v_a_851_, v_snd_855_);
return v___x_860_;
}
case 3:
{
lean_object* v___x_861_; 
lean_dec(v_offset_849_);
lean_dec_ref(v___x_843_);
v___x_861_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_853_, v_e_848_, v_a_850_, v_a_851_, v_snd_855_);
return v___x_861_;
}
default: 
{
lean_object* v___x_862_; lean_object* v_fst_863_; lean_object* v_snd_864_; lean_object* v_fst_865_; lean_object* v_snd_866_; lean_object* v___x_867_; 
v___x_862_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v_minIndex_842_, v___x_843_, v___x_844_, v_start_845_, v_xs_846_, v___x_847_, v_e_848_, v_offset_849_, v_a_850_, v_a_851_, v_snd_855_);
v_fst_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_fst_863_);
v_snd_864_ = lean_ctor_get(v___x_862_, 1);
lean_inc(v_snd_864_);
lean_dec_ref(v___x_862_);
v_fst_865_ = lean_ctor_get(v_fst_863_, 0);
lean_inc(v_fst_865_);
v_snd_866_ = lean_ctor_get(v_fst_863_, 1);
lean_inc(v_snd_866_);
lean_dec(v_fst_863_);
v___x_867_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_853_, v_fst_865_, v_snd_866_, v_a_851_, v_snd_864_);
return v___x_867_;
}
}
}
v___jp_868_:
{
lean_object* v_maxIndex_870_; uint8_t v___x_871_; 
v_maxIndex_870_ = l_Lean_LocalDecl_index(v___y_869_);
lean_dec_ref(v___y_869_);
v___x_871_ = lean_nat_dec_lt(v_maxIndex_870_, v_minIndex_842_);
lean_dec(v_maxIndex_870_);
if (v___x_871_ == 0)
{
v_snd_855_ = v_a_852_;
goto v___jp_854_;
}
else
{
lean_object* v___x_872_; 
lean_dec(v_offset_849_);
lean_dec_ref(v___x_843_);
v___x_872_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_853_, v_e_848_, v_a_850_, v_a_851_, v_a_852_);
return v___x_872_;
}
}
v___jp_873_:
{
lean_object* v___x_875_; 
lean_inc_ref(v___x_843_);
v___x_875_ = lean_local_ctx_find(v___x_843_, v___y_874_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_877_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v___x_876_);
v___y_869_ = v___x_877_;
goto v___jp_868_;
}
else
{
lean_object* v_val_878_; 
v_val_878_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_val_878_);
lean_dec_ref(v___x_875_);
v___y_869_ = v_val_878_;
goto v___jp_868_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6___boxed(lean_object* v_minIndex_907_, lean_object* v___x_908_, lean_object* v___x_909_, lean_object* v_start_910_, lean_object* v_xs_911_, lean_object* v___x_912_, lean_object* v_e_913_, lean_object* v_offset_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
uint8_t v_a_boxed_918_; lean_object* v_res_919_; 
v_a_boxed_918_ = lean_unbox(v_a_916_);
v_res_919_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_907_, v___x_908_, v___x_909_, v_start_910_, v_xs_911_, v___x_912_, v_e_913_, v_offset_914_, v_a_915_, v_a_boxed_918_, v_a_917_);
lean_dec_ref(v___x_912_);
lean_dec_ref(v_xs_911_);
lean_dec(v_start_910_);
lean_dec(v___x_909_);
lean_dec(v_minIndex_907_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___boxed(lean_object* v_minIndex_920_, lean_object* v___x_921_, lean_object* v___x_922_, lean_object* v_start_923_, lean_object* v_xs_924_, lean_object* v___x_925_, lean_object* v_e_926_, lean_object* v_offset_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
uint8_t v_a_boxed_931_; lean_object* v_res_932_; 
v_a_boxed_931_ = lean_unbox(v_a_929_);
v_res_932_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v_minIndex_920_, v___x_921_, v___x_922_, v_start_923_, v_xs_924_, v___x_925_, v_e_926_, v_offset_927_, v_a_928_, v_a_boxed_931_, v_a_930_);
lean_dec_ref(v___x_925_);
lean_dec_ref(v_xs_924_);
lean_dec(v_start_923_);
lean_dec(v___x_922_);
lean_dec(v_minIndex_920_);
return v_res_932_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0(void){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(lean_box(0));
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___redArg(lean_object* v_e_934_, lean_object* v_start_935_, lean_object* v_xs_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
uint8_t v___x_940_; 
v___x_940_ = l_Lean_Expr_hasFVar(v_e_934_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; 
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v_e_934_);
return v___x_941_;
}
else
{
lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_942_ = lean_array_get_size(v_xs_936_);
v___x_943_ = lean_nat_dec_lt(v_start_935_, v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; 
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v_e_934_);
return v___x_944_;
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v_share_947_; lean_object* v_maxFVar_948_; lean_object* v_proofInstInfo_949_; lean_object* v_inferType_950_; lean_object* v_getLevel_951_; lean_object* v_congrInfo_952_; lean_object* v_defEqI_953_; lean_object* v_extensions_954_; lean_object* v_issues_955_; lean_object* v_canon_956_; uint8_t v_debug_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_1041_; 
v___x_945_ = lean_st_ref_get(v_a_937_);
v___x_946_ = lean_st_ref_take(v_a_937_);
v_share_947_ = lean_ctor_get(v___x_946_, 0);
v_maxFVar_948_ = lean_ctor_get(v___x_946_, 1);
v_proofInstInfo_949_ = lean_ctor_get(v___x_946_, 2);
v_inferType_950_ = lean_ctor_get(v___x_946_, 3);
v_getLevel_951_ = lean_ctor_get(v___x_946_, 4);
v_congrInfo_952_ = lean_ctor_get(v___x_946_, 5);
v_defEqI_953_ = lean_ctor_get(v___x_946_, 6);
v_extensions_954_ = lean_ctor_get(v___x_946_, 7);
v_issues_955_ = lean_ctor_get(v___x_946_, 8);
v_canon_956_ = lean_ctor_get(v___x_946_, 9);
v_debug_957_ = lean_ctor_get_uint8(v___x_946_, sizeof(void*)*10);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_959_ = v___x_946_;
v_isShared_960_ = v_isSharedCheck_1041_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_canon_956_);
lean_inc(v_issues_955_);
lean_inc(v_extensions_954_);
lean_inc(v_defEqI_953_);
lean_inc(v_congrInfo_952_);
lean_inc(v_getLevel_951_);
lean_inc(v_inferType_950_);
lean_inc(v_proofInstInfo_949_);
lean_inc(v_maxFVar_948_);
lean_inc(v_share_947_);
lean_dec(v___x_946_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_1041_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lean_obj_once(&l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0, &l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0_once, _init_l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 0, v___x_961_);
v___x_963_ = v___x_959_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_maxFVar_948_);
lean_ctor_set(v_reuseFailAlloc_1040_, 2, v_proofInstInfo_949_);
lean_ctor_set(v_reuseFailAlloc_1040_, 3, v_inferType_950_);
lean_ctor_set(v_reuseFailAlloc_1040_, 4, v_getLevel_951_);
lean_ctor_set(v_reuseFailAlloc_1040_, 5, v_congrInfo_952_);
lean_ctor_set(v_reuseFailAlloc_1040_, 6, v_defEqI_953_);
lean_ctor_set(v_reuseFailAlloc_1040_, 7, v_extensions_954_);
lean_ctor_set(v_reuseFailAlloc_1040_, 8, v_issues_955_);
lean_ctor_set(v_reuseFailAlloc_1040_, 9, v_canon_956_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, sizeof(void*)*10, v_debug_957_);
v___x_963_ = v_reuseFailAlloc_1040_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v_fst_967_; lean_object* v_snd_968_; lean_object* v_lctx_990_; lean_object* v_maxFVar_991_; uint8_t v_debug_992_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v_snd_996_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1018_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_964_ = lean_st_ref_set(v_a_937_, v___x_963_);
v___x_965_ = lean_st_ref_get(v_a_937_);
v_lctx_990_ = lean_ctor_get(v_a_938_, 2);
v_maxFVar_991_ = lean_ctor_get(v___x_945_, 1);
lean_inc_ref(v_maxFVar_991_);
lean_dec(v___x_945_);
v_debug_992_ = lean_ctor_get_uint8(v___x_965_, sizeof(void*)*10);
lean_dec(v___x_965_);
v___x_1034_ = lean_array_fget_borrowed(v_xs_936_, v_start_935_);
v___x_1035_ = l_Lean_Expr_fvarId_x21(v___x_1034_);
lean_inc_ref(v_lctx_990_);
v___x_1036_ = lean_local_ctx_find(v_lctx_990_, v___x_1035_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1038_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v___x_1037_);
v___y_1018_ = v___x_1038_;
goto v___jp_1017_;
}
else
{
lean_object* v_val_1039_; 
v_val_1039_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_val_1039_);
lean_dec_ref(v___x_1036_);
v___y_1018_ = v_val_1039_;
goto v___jp_1017_;
}
v___jp_966_:
{
lean_object* v___x_969_; lean_object* v_maxFVar_970_; lean_object* v_proofInstInfo_971_; lean_object* v_inferType_972_; lean_object* v_getLevel_973_; lean_object* v_congrInfo_974_; lean_object* v_defEqI_975_; lean_object* v_extensions_976_; lean_object* v_issues_977_; lean_object* v_canon_978_; uint8_t v_debug_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_988_; 
v___x_969_ = lean_st_ref_take(v_a_937_);
v_maxFVar_970_ = lean_ctor_get(v___x_969_, 1);
v_proofInstInfo_971_ = lean_ctor_get(v___x_969_, 2);
v_inferType_972_ = lean_ctor_get(v___x_969_, 3);
v_getLevel_973_ = lean_ctor_get(v___x_969_, 4);
v_congrInfo_974_ = lean_ctor_get(v___x_969_, 5);
v_defEqI_975_ = lean_ctor_get(v___x_969_, 6);
v_extensions_976_ = lean_ctor_get(v___x_969_, 7);
v_issues_977_ = lean_ctor_get(v___x_969_, 8);
v_canon_978_ = lean_ctor_get(v___x_969_, 9);
v_debug_979_ = lean_ctor_get_uint8(v___x_969_, sizeof(void*)*10);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; 
v_unused_989_ = lean_ctor_get(v___x_969_, 0);
lean_dec(v_unused_989_);
v___x_981_ = v___x_969_;
v_isShared_982_ = v_isSharedCheck_988_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_canon_978_);
lean_inc(v_issues_977_);
lean_inc(v_extensions_976_);
lean_inc(v_defEqI_975_);
lean_inc(v_congrInfo_974_);
lean_inc(v_getLevel_973_);
lean_inc(v_inferType_972_);
lean_inc(v_proofInstInfo_971_);
lean_inc(v_maxFVar_970_);
lean_dec(v___x_969_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_988_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v_snd_968_);
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_snd_968_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v_maxFVar_970_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_proofInstInfo_971_);
lean_ctor_set(v_reuseFailAlloc_987_, 3, v_inferType_972_);
lean_ctor_set(v_reuseFailAlloc_987_, 4, v_getLevel_973_);
lean_ctor_set(v_reuseFailAlloc_987_, 5, v_congrInfo_974_);
lean_ctor_set(v_reuseFailAlloc_987_, 6, v_defEqI_975_);
lean_ctor_set(v_reuseFailAlloc_987_, 7, v_extensions_976_);
lean_ctor_set(v_reuseFailAlloc_987_, 8, v_issues_977_);
lean_ctor_set(v_reuseFailAlloc_987_, 9, v_canon_978_);
lean_ctor_set_uint8(v_reuseFailAlloc_987_, sizeof(void*)*10, v_debug_979_);
v___x_984_ = v_reuseFailAlloc_987_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_st_ref_set(v_a_937_, v___x_984_);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v_fst_967_);
return v___x_986_;
}
}
}
v___jp_993_:
{
switch(lean_obj_tag(v_e_934_))
{
case 9:
{
lean_dec(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v_maxFVar_991_);
v_fst_967_ = v_e_934_;
v_snd_968_ = v_snd_996_;
goto v___jp_966_;
}
case 2:
{
lean_dec(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v_maxFVar_991_);
v_fst_967_ = v_e_934_;
v_snd_968_ = v_snd_996_;
goto v___jp_966_;
}
case 0:
{
lean_dec(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v_maxFVar_991_);
v_fst_967_ = v_e_934_;
v_snd_968_ = v_snd_996_;
goto v___jp_966_;
}
case 1:
{
lean_dec(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v_maxFVar_991_);
v_fst_967_ = v_e_934_;
v_snd_968_ = v_snd_996_;
goto v___jp_966_;
}
case 4:
{
lean_dec(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v_maxFVar_991_);
v_fst_967_ = v_e_934_;
v_snd_968_ = v_snd_996_;
goto v___jp_966_;
}
case 3:
{
lean_dec(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v_maxFVar_991_);
v_fst_967_ = v_e_934_;
v_snd_968_ = v_snd_996_;
goto v___jp_966_;
}
default: 
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v_fst_1000_; lean_object* v_snd_1001_; lean_object* v_fst_1002_; 
v___x_997_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0);
lean_inc(v___y_994_);
v___x_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_998_, 0, v___y_994_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
lean_inc_ref(v_lctx_990_);
v___x_999_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v___y_995_, v_lctx_990_, v___x_942_, v_start_935_, v_xs_936_, v_maxFVar_991_, v_e_934_, v___y_994_, v___x_998_, v_debug_992_, v_snd_996_);
lean_dec_ref(v_maxFVar_991_);
lean_dec(v___y_995_);
v_fst_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_fst_1000_);
v_snd_1001_ = lean_ctor_get(v___x_999_, 1);
lean_inc(v_snd_1001_);
lean_dec_ref(v___x_999_);
v_fst_1002_ = lean_ctor_get(v_fst_1000_, 0);
lean_inc(v_fst_1002_);
lean_dec(v_fst_1000_);
v_fst_967_ = v_fst_1002_;
v_snd_968_ = v_snd_1001_;
goto v___jp_966_;
}
}
}
v___jp_1003_:
{
lean_object* v_maxIndex_1007_; uint8_t v___x_1008_; 
v_maxIndex_1007_ = l_Lean_LocalDecl_index(v___y_1006_);
lean_dec_ref(v___y_1006_);
v___x_1008_ = lean_nat_dec_lt(v_maxIndex_1007_, v___y_1005_);
lean_dec(v_maxIndex_1007_);
if (v___x_1008_ == 0)
{
v___y_994_ = v___y_1004_;
v___y_995_ = v___y_1005_;
v_snd_996_ = v_share_947_;
goto v___jp_993_;
}
else
{
lean_dec(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v_maxFVar_991_);
v_fst_967_ = v_e_934_;
v_snd_968_ = v_share_947_;
goto v___jp_966_;
}
}
v___jp_1009_:
{
lean_object* v___x_1013_; 
lean_inc_ref(v_lctx_990_);
v___x_1013_ = lean_local_ctx_find(v_lctx_990_, v___y_1012_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1015_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v___x_1014_);
v___y_1004_ = v___y_1010_;
v___y_1005_ = v___y_1011_;
v___y_1006_ = v___x_1015_;
goto v___jp_1003_;
}
else
{
lean_object* v_val_1016_; 
v_val_1016_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_val_1016_);
lean_dec_ref(v___x_1013_);
v___y_1004_ = v___y_1010_;
v___y_1005_ = v___y_1011_;
v___y_1006_ = v_val_1016_;
goto v___jp_1003_;
}
}
v___jp_1017_:
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_934_))
{
case 1:
{
lean_object* v_fvarId_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_dec_ref(v___y_1018_);
lean_dec_ref(v_maxFVar_991_);
v_fvarId_1020_ = lean_ctor_get(v_e_934_, 0);
v___x_1021_ = lean_unsigned_to_nat(1u);
v___x_1022_ = lean_nat_sub(v___x_942_, v___x_1021_);
v___x_1023_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_935_, v_xs_936_, v_fvarId_1020_, v___x_1019_, v___x_1022_);
if (lean_obj_tag(v___x_1023_) == 1)
{
lean_object* v_val_1024_; lean_object* v___x_1025_; lean_object* v_fst_1026_; lean_object* v_snd_1027_; 
lean_dec_ref(v_e_934_);
v_val_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_val_1024_);
lean_dec_ref(v___x_1023_);
v___x_1025_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_val_1024_, v_share_947_);
v_fst_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_fst_1026_);
v_snd_1027_ = lean_ctor_get(v___x_1025_, 1);
lean_inc(v_snd_1027_);
lean_dec_ref(v___x_1025_);
v_fst_967_ = v_fst_1026_;
v_snd_968_ = v_snd_1027_;
goto v___jp_966_;
}
else
{
lean_dec(v___x_1023_);
v_fst_967_ = v_e_934_;
v_snd_968_ = v_share_947_;
goto v___jp_966_;
}
}
case 9:
{
lean_dec_ref(v___y_1018_);
lean_dec_ref(v_maxFVar_991_);
v_fst_967_ = v_e_934_;
v_snd_968_ = v_share_947_;
goto v___jp_966_;
}
case 2:
{
lean_dec_ref(v___y_1018_);
lean_dec_ref(v_maxFVar_991_);
v_fst_967_ = v_e_934_;
v_snd_968_ = v_share_947_;
goto v___jp_966_;
}
case 0:
{
lean_dec_ref(v___y_1018_);
lean_dec_ref(v_maxFVar_991_);
v_fst_967_ = v_e_934_;
v_snd_968_ = v_share_947_;
goto v___jp_966_;
}
case 4:
{
lean_dec_ref(v___y_1018_);
lean_dec_ref(v_maxFVar_991_);
v_fst_967_ = v_e_934_;
v_snd_968_ = v_share_947_;
goto v___jp_966_;
}
case 3:
{
lean_dec_ref(v___y_1018_);
lean_dec_ref(v_maxFVar_991_);
v_fst_967_ = v_e_934_;
v_snd_968_ = v_share_947_;
goto v___jp_966_;
}
default: 
{
if (v___x_940_ == 0)
{
lean_dec_ref(v___y_1018_);
lean_dec_ref(v_maxFVar_991_);
v_fst_967_ = v_e_934_;
v_snd_968_ = v_share_947_;
goto v___jp_966_;
}
else
{
lean_object* v_minIndex_1028_; lean_object* v___x_1029_; 
v_minIndex_1028_ = l_Lean_LocalDecl_index(v___y_1018_);
lean_dec_ref(v___y_1018_);
v___x_1029_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(v_maxFVar_991_, v_e_934_);
if (lean_obj_tag(v___x_1029_) == 1)
{
lean_object* v_val_1030_; 
v_val_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_val_1030_);
lean_dec_ref(v___x_1029_);
if (lean_obj_tag(v_val_1030_) == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1032_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v___x_1031_);
v___y_1010_ = v___x_1019_;
v___y_1011_ = v_minIndex_1028_;
v___y_1012_ = v___x_1032_;
goto v___jp_1009_;
}
else
{
lean_object* v_val_1033_; 
v_val_1033_ = lean_ctor_get(v_val_1030_, 0);
lean_inc(v_val_1033_);
lean_dec_ref(v_val_1030_);
v___y_1010_ = v___x_1019_;
v___y_1011_ = v_minIndex_1028_;
v___y_1012_ = v_val_1033_;
goto v___jp_1009_;
}
}
else
{
lean_dec(v___x_1029_);
v___y_994_ = v___x_1019_;
v___y_995_ = v_minIndex_1028_;
v_snd_996_ = v_share_947_;
goto v___jp_993_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___redArg___boxed(lean_object* v_e_1042_, lean_object* v_start_1043_, lean_object* v_xs_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v_e_1042_, v_start_1043_, v_xs_1044_, v_a_1045_, v_a_1046_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_xs_1044_);
lean_dec(v_start_1043_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange(lean_object* v_e_1049_, lean_object* v_start_1050_, lean_object* v_xs_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v_e_1049_, v_start_1050_, v_xs_1051_, v_a_1053_, v_a_1054_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___boxed(lean_object* v_e_1060_, lean_object* v_start_1061_, lean_object* v_xs_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1060_, v_start_1061_, v_xs_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
lean_dec_ref(v_xs_1062_);
lean_dec(v_start_1061_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(lean_object* v_00_u03b2_1071_, lean_object* v_x_1072_, lean_object* v_x_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(v_x_1072_, v_x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___boxed(lean_object* v_00_u03b2_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(v_00_u03b2_1075_, v_x_1076_, v_x_1077_);
lean_dec_ref(v_x_1077_);
lean_dec_ref(v_x_1076_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3(lean_object* v_00_u03b2_1079_, lean_object* v_x_1080_, size_t v_x_1081_, lean_object* v_x_1082_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(v_x_1080_, v_x_1081_, v_x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___boxed(lean_object* v_00_u03b2_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_){
_start:
{
size_t v_x_26629__boxed_1088_; lean_object* v_res_1089_; 
v_x_26629__boxed_1088_ = lean_unbox_usize(v_x_1086_);
lean_dec(v_x_1086_);
v_res_1089_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3(v_00_u03b2_1084_, v_x_1085_, v_x_26629__boxed_1088_, v_x_1087_);
lean_dec_ref(v_x_1087_);
lean_dec_ref(v_x_1085_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5(lean_object* v_00_u03b2_1090_, lean_object* v_keys_1091_, lean_object* v_vals_1092_, lean_object* v_heq_1093_, lean_object* v_i_1094_, lean_object* v_k_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg(v_keys_1091_, v_vals_1092_, v_i_1094_, v_k_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1097_, lean_object* v_keys_1098_, lean_object* v_vals_1099_, lean_object* v_heq_1100_, lean_object* v_i_1101_, lean_object* v_k_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5(v_00_u03b2_1097_, v_keys_1098_, v_vals_1099_, v_heq_1100_, v_i_1101_, v_k_1102_);
lean_dec_ref(v_k_1102_);
lean_dec_ref(v_vals_1099_);
lean_dec_ref(v_keys_1098_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_1104_, lean_object* v_m_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg(v_m_1105_, v_a_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1108_, lean_object* v_m_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8(v_00_u03b2_1108_, v_m_1109_, v_a_1110_);
lean_dec_ref(v_a_1110_);
lean_dec_ref(v_m_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16(lean_object* v_00_u03b2_1112_, lean_object* v_a_1113_, lean_object* v_x_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___redArg(v_a_1113_, v_x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___boxed(lean_object* v_00_u03b2_1116_, lean_object* v_a_1117_, lean_object* v_x_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16(v_00_u03b2_1116_, v_a_1117_, v_x_1118_);
lean_dec(v_x_1118_);
lean_dec_ref(v_a_1117_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars___redArg(lean_object* v_e_1120_, lean_object* v_xs_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_unsigned_to_nat(0u);
v___x_1126_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v_e_1120_, v___x_1125_, v_xs_1121_, v_a_1122_, v_a_1123_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars___redArg___boxed(lean_object* v_e_1127_, lean_object* v_xs_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_Meta_Sym_abstractFVars___redArg(v_e_1127_, v_xs_1128_, v_a_1129_, v_a_1130_);
lean_dec_ref(v_a_1130_);
lean_dec(v_a_1129_);
lean_dec_ref(v_xs_1128_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars(lean_object* v_e_1133_, lean_object* v_xs_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_unsigned_to_nat(0u);
v___x_1143_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v_e_1133_, v___x_1142_, v_xs_1134_, v_a_1136_, v_a_1137_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars___boxed(lean_object* v_e_1144_, lean_object* v_xs_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_Meta_Sym_abstractFVars(v_e_1144_, v_xs_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec_ref(v_xs_1145_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(lean_object* v_x_1154_, uint8_t v_bi_1155_, lean_object* v_t_1156_, lean_object* v_b_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v___y_1166_; lean_object* v___x_1169_; uint8_t v_debug_1170_; 
v___x_1169_ = lean_st_ref_get(v___y_1159_);
v_debug_1170_ = lean_ctor_get_uint8(v___x_1169_, sizeof(void*)*10);
lean_dec(v___x_1169_);
if (v_debug_1170_ == 0)
{
v___y_1166_ = v___y_1159_;
goto v___jp_1165_;
}
else
{
lean_object* v___x_1171_; 
lean_inc_ref(v_t_1156_);
v___x_1171_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1156_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v___x_1172_; 
lean_dec_ref(v___x_1171_);
lean_inc_ref(v_b_1157_);
v___x_1172_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_dec_ref(v___x_1172_);
v___y_1166_ = v___y_1159_;
goto v___jp_1165_;
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec_ref(v_b_1157_);
lean_dec_ref(v_t_1156_);
lean_dec(v_x_1154_);
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1172_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec_ref(v_b_1157_);
lean_dec_ref(v_t_1156_);
lean_dec(v_x_1154_);
v_a_1181_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1171_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1171_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
v___jp_1165_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = l_Lean_Expr_lam___override(v_x_1154_, v_t_1156_, v_b_1157_, v_bi_1155_);
v___x_1168_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1167_, v___y_1166_);
return v___x_1168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0___boxed(lean_object* v_x_1189_, lean_object* v_bi_1190_, lean_object* v_t_1191_, lean_object* v_b_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
uint8_t v_bi_boxed_1200_; lean_object* v_res_1201_; 
v_bi_boxed_1200_ = lean_unbox(v_bi_1190_);
v_res_1201_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v_x_1189_, v_bi_boxed_1200_, v_t_1191_, v_b_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(lean_object* v_xs_1202_, lean_object* v_i_1203_, lean_object* v_a_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_zero_1212_; uint8_t v_isZero_1213_; 
v_zero_1212_ = lean_unsigned_to_nat(0u);
v_isZero_1213_ = lean_nat_dec_eq(v_i_1203_, v_zero_1212_);
if (v_isZero_1213_ == 1)
{
lean_object* v___x_1214_; 
lean_dec(v_i_1203_);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v_a_1204_);
return v___x_1214_;
}
else
{
lean_object* v_one_1215_; lean_object* v_n_1216_; lean_object* v___y_1218_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v_one_1215_ = lean_unsigned_to_nat(1u);
v_n_1216_ = lean_nat_sub(v_i_1203_, v_one_1215_);
lean_dec(v_i_1203_);
v___x_1221_ = lean_array_fget_borrowed(v_xs_1202_, v_n_1216_);
v___x_1222_ = l_Lean_Expr_fvarId_x21(v___x_1221_);
v___x_1223_ = l_Lean_FVarId_getDecl___redArg(v___x_1222_, v___y_1207_, v___y_1209_, v___y_1210_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v_a_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v_a_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; lean_object* v___x_1230_; 
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_a_1224_);
lean_dec_ref(v___x_1223_);
v___x_1225_ = l_Lean_LocalDecl_type(v_a_1224_);
v___x_1226_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v___x_1225_, v_n_1216_, v_xs_1202_, v___y_1206_, v___y_1207_);
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1227_);
lean_dec_ref(v___x_1226_);
v___x_1228_ = l_Lean_LocalDecl_userName(v_a_1224_);
v___x_1229_ = l_Lean_LocalDecl_binderInfo(v_a_1224_);
lean_dec(v_a_1224_);
v___x_1230_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v___x_1228_, v___x_1229_, v_a_1227_, v_a_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
v___y_1218_ = v___x_1230_;
goto v___jp_1217_;
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec(v_n_1216_);
lean_dec_ref(v_a_1204_);
v_a_1231_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1223_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1223_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
v___jp_1217_:
{
if (lean_obj_tag(v___y_1218_) == 0)
{
lean_object* v_a_1219_; 
v_a_1219_ = lean_ctor_get(v___y_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref(v___y_1218_);
v_i_1203_ = v_n_1216_;
v_a_1204_ = v_a_1219_;
goto _start;
}
else
{
lean_dec(v_n_1216_);
return v___y_1218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg___boxed(lean_object* v_xs_1239_, lean_object* v_i_1240_, lean_object* v_a_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1239_, v_i_1240_, v_a_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec_ref(v_xs_1239_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS(lean_object* v_xs_1250_, lean_object* v_e_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v_a_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1259_ = lean_unsigned_to_nat(0u);
v___x_1260_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v_e_1251_, v___x_1259_, v_xs_1250_, v_a_1253_, v_a_1254_);
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref(v___x_1260_);
v___x_1262_ = lean_array_get_size(v_xs_1250_);
v___x_1263_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1250_, v___x_1262_, v_a_1261_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS___boxed(lean_object* v_xs_1264_, lean_object* v_e_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_1264_, v_e_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec_ref(v_xs_1264_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(lean_object* v_xs_1274_, lean_object* v_n_1275_, lean_object* v_i_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1274_, v_i_1276_, v_a_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___boxed(lean_object* v_xs_1287_, lean_object* v_n_1288_, lean_object* v_i_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(v_xs_1287_, v_n_1288_, v_i_1289_, v_a_1290_, v_a_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v_n_1288_);
lean_dec_ref(v_xs_1287_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(lean_object* v_x_1300_, uint8_t v_bi_1301_, lean_object* v_t_1302_, lean_object* v_b_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___y_1312_; lean_object* v___x_1315_; uint8_t v_debug_1316_; 
v___x_1315_ = lean_st_ref_get(v___y_1305_);
v_debug_1316_ = lean_ctor_get_uint8(v___x_1315_, sizeof(void*)*10);
lean_dec(v___x_1315_);
if (v_debug_1316_ == 0)
{
v___y_1312_ = v___y_1305_;
goto v___jp_1311_;
}
else
{
lean_object* v___x_1317_; 
lean_inc_ref(v_t_1302_);
v___x_1317_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1302_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v___x_1318_; 
lean_dec_ref(v___x_1317_);
lean_inc_ref(v_b_1303_);
v___x_1318_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_dec_ref(v___x_1318_);
v___y_1312_ = v___y_1305_;
goto v___jp_1311_;
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec_ref(v_b_1303_);
lean_dec_ref(v_t_1302_);
lean_dec(v_x_1300_);
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec_ref(v_b_1303_);
lean_dec_ref(v_t_1302_);
lean_dec(v_x_1300_);
v_a_1327_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1317_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1317_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
v___jp_1311_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = l_Lean_Expr_forallE___override(v_x_1300_, v_t_1302_, v_b_1303_, v_bi_1301_);
v___x_1314_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1313_, v___y_1312_);
return v___x_1314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0___boxed(lean_object* v_x_1335_, lean_object* v_bi_1336_, lean_object* v_t_1337_, lean_object* v_b_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
uint8_t v_bi_boxed_1346_; lean_object* v_res_1347_; 
v_bi_boxed_1346_ = lean_unbox(v_bi_1336_);
v_res_1347_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v_x_1335_, v_bi_boxed_1346_, v_t_1337_, v_b_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(lean_object* v_xs_1348_, lean_object* v_i_1349_, lean_object* v_a_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v_zero_1358_; uint8_t v_isZero_1359_; 
v_zero_1358_ = lean_unsigned_to_nat(0u);
v_isZero_1359_ = lean_nat_dec_eq(v_i_1349_, v_zero_1358_);
if (v_isZero_1359_ == 1)
{
lean_object* v___x_1360_; 
lean_dec(v_i_1349_);
v___x_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1360_, 0, v_a_1350_);
return v___x_1360_;
}
else
{
lean_object* v_one_1361_; lean_object* v_n_1362_; lean_object* v___y_1364_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v_one_1361_ = lean_unsigned_to_nat(1u);
v_n_1362_ = lean_nat_sub(v_i_1349_, v_one_1361_);
lean_dec(v_i_1349_);
v___x_1367_ = lean_array_fget_borrowed(v_xs_1348_, v_n_1362_);
v___x_1368_ = l_Lean_Expr_fvarId_x21(v___x_1367_);
v___x_1369_ = l_Lean_FVarId_getDecl___redArg(v___x_1368_, v___y_1353_, v___y_1355_, v___y_1356_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v_a_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; lean_object* v___x_1376_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref(v___x_1369_);
v___x_1371_ = l_Lean_LocalDecl_type(v_a_1370_);
v___x_1372_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v___x_1371_, v_n_1362_, v_xs_1348_, v___y_1352_, v___y_1353_);
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref(v___x_1372_);
v___x_1374_ = l_Lean_LocalDecl_userName(v_a_1370_);
v___x_1375_ = l_Lean_LocalDecl_binderInfo(v_a_1370_);
lean_dec(v_a_1370_);
v___x_1376_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v___x_1374_, v___x_1375_, v_a_1373_, v_a_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
v___y_1364_ = v___x_1376_;
goto v___jp_1363_;
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec(v_n_1362_);
lean_dec_ref(v_a_1350_);
v_a_1377_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1369_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1369_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
v___jp_1363_:
{
if (lean_obj_tag(v___y_1364_) == 0)
{
lean_object* v_a_1365_; 
v_a_1365_ = lean_ctor_get(v___y_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref(v___y_1364_);
v_i_1349_ = v_n_1362_;
v_a_1350_ = v_a_1365_;
goto _start;
}
else
{
lean_dec(v_n_1362_);
return v___y_1364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg___boxed(lean_object* v_xs_1385_, lean_object* v_i_1386_, lean_object* v_a_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1385_, v_i_1386_, v_a_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec_ref(v_xs_1385_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS(lean_object* v_xs_1396_, lean_object* v_e_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v_a_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1405_ = lean_unsigned_to_nat(0u);
v___x_1406_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v_e_1397_, v___x_1405_, v_xs_1396_, v_a_1399_, v_a_1400_);
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref(v___x_1406_);
v___x_1408_ = lean_array_get_size(v_xs_1396_);
v___x_1409_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1396_, v___x_1408_, v_a_1407_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS___boxed(lean_object* v_xs_1410_, lean_object* v_e_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_Meta_Sym_mkForallFVarsS(v_xs_1410_, v_e_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_);
lean_dec(v_a_1417_);
lean_dec_ref(v_a_1416_);
lean_dec(v_a_1415_);
lean_dec_ref(v_a_1414_);
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
lean_dec_ref(v_xs_1410_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(lean_object* v_xs_1420_, lean_object* v_n_1421_, lean_object* v_i_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1420_, v_i_1422_, v_a_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___boxed(lean_object* v_xs_1433_, lean_object* v_n_1434_, lean_object* v_i_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(v_xs_1433_, v_n_1434_, v_i_1435_, v_a_1436_, v_a_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v_n_1434_);
lean_dec_ref(v_xs_1433_);
return v_res_1445_;
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
