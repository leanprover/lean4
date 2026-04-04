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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_maxFVar_14_);
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
lean_dec_ref(v_maxFVar_14_);
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
lean_dec_ref(v_maxFVar_14_);
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
lean_dec_ref(v_maxFVar_14_);
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
lean_dec_ref(v_maxFVar_14_);
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
lean_dec_ref(v_maxFVar_14_);
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
lean_dec_ref(v_maxFVar_14_);
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
lean_object* v_es_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_564_; 
v_es_543_ = lean_ctor_get(v_x_540_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v_x_540_);
if (v_isSharedCheck_564_ == 0)
{
v___x_545_ = v_x_540_;
v_isShared_546_ = v_isSharedCheck_564_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_es_543_);
lean_dec(v_x_540_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_564_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; size_t v___x_548_; size_t v___x_549_; size_t v___x_550_; lean_object* v_j_551_; lean_object* v___x_552_; 
v___x_547_ = lean_box(2);
v___x_548_ = ((size_t)5ULL);
v___x_549_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1);
v___x_550_ = lean_usize_land(v_x_541_, v___x_549_);
v_j_551_ = lean_usize_to_nat(v___x_550_);
v___x_552_ = lean_array_get(v___x_547_, v_es_543_, v_j_551_);
lean_dec(v_j_551_);
lean_dec_ref(v_es_543_);
switch(lean_obj_tag(v___x_552_))
{
case 0:
{
lean_object* v_key_553_; lean_object* v_val_554_; uint8_t v___x_555_; 
v_key_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_key_553_);
v_val_554_ = lean_ctor_get(v___x_552_, 1);
lean_inc(v_val_554_);
lean_dec_ref(v___x_552_);
v___x_555_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_542_, v_key_553_);
lean_dec(v_key_553_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
lean_dec(v_val_554_);
lean_del_object(v___x_545_);
v___x_556_ = lean_box(0);
return v___x_556_;
}
else
{
lean_object* v___x_558_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set_tag(v___x_545_, 1);
lean_ctor_set(v___x_545_, 0, v_val_554_);
v___x_558_ = v___x_545_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_val_554_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
case 1:
{
lean_object* v_node_560_; size_t v___x_561_; 
lean_del_object(v___x_545_);
v_node_560_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_node_560_);
lean_dec_ref(v___x_552_);
v___x_561_ = lean_usize_shift_right(v_x_541_, v___x_548_);
v_x_540_ = v_node_560_;
v_x_541_ = v___x_561_;
goto _start;
}
default: 
{
lean_object* v___x_563_; 
lean_del_object(v___x_545_);
v___x_563_ = lean_box(0);
return v___x_563_;
}
}
}
}
else
{
lean_object* v_ks_565_; lean_object* v_vs_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_ks_565_ = lean_ctor_get(v_x_540_, 0);
lean_inc_ref(v_ks_565_);
v_vs_566_ = lean_ctor_get(v_x_540_, 1);
lean_inc_ref(v_vs_566_);
lean_dec_ref(v_x_540_);
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg(v_ks_565_, v_vs_566_, v___x_567_, v_x_542_);
lean_dec_ref(v_vs_566_);
lean_dec_ref(v_ks_565_);
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___boxed(lean_object* v_x_569_, lean_object* v_x_570_, lean_object* v_x_571_){
_start:
{
size_t v_x_25664__boxed_572_; lean_object* v_res_573_; 
v_x_25664__boxed_572_ = lean_unbox_usize(v_x_570_);
lean_dec(v_x_570_);
v_res_573_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(v_x_569_, v_x_25664__boxed_572_, v_x_571_);
lean_dec_ref(v_x_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(lean_object* v_x_574_, lean_object* v_x_575_){
_start:
{
uint64_t v___x_576_; size_t v___x_577_; lean_object* v___x_578_; 
v___x_576_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_575_);
v___x_577_ = lean_uint64_to_usize(v___x_576_);
v___x_578_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(v_x_574_, v___x_577_, v_x_575_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg___boxed(lean_object* v_x_579_, lean_object* v_x_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(v_x_579_, v_x_580_);
lean_dec_ref(v_x_580_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13(lean_object* v_msg_589_, lean_object* v___y_590_, uint8_t v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___f_593_; lean_object* v___f_594_; lean_object* v___f_595_; lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___f_603_; lean_object* v___f_604_; lean_object* v___f_605_; lean_object* v___f_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___f_614_; lean_object* v___f_615_; lean_object* v___f_616_; lean_object* v___f_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_24871__overap_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___f_593_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__0));
v___f_594_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__1));
v___f_595_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__2));
v___f_596_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__3));
v___f_597_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__4));
v___f_598_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__5));
v___f_599_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__6));
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___f_593_);
lean_ctor_set(v___x_600_, 1, v___f_594_);
v___x_601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v___f_595_);
lean_ctor_set(v___x_601_, 2, v___f_596_);
lean_ctor_set(v___x_601_, 3, v___f_597_);
lean_ctor_set(v___x_601_, 4, v___f_598_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___f_599_);
lean_inc_ref_n(v___x_602_, 6);
v___f_603_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_603_, 0, v___x_602_);
v___f_604_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_604_, 0, v___x_602_);
v___f_605_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_605_, 0, v___x_602_);
v___f_606_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_606_, 0, v___x_602_);
v___x_607_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_607_, 0, lean_box(0));
lean_closure_set(v___x_607_, 1, lean_box(0));
lean_closure_set(v___x_607_, 2, v___x_602_);
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v___f_603_);
v___x_609_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_609_, 0, lean_box(0));
lean_closure_set(v___x_609_, 1, lean_box(0));
lean_closure_set(v___x_609_, 2, v___x_602_);
v___x_610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
lean_ctor_set(v___x_610_, 2, v___f_604_);
lean_ctor_set(v___x_610_, 3, v___f_605_);
lean_ctor_set(v___x_610_, 4, v___f_606_);
v___x_611_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_611_, 0, lean_box(0));
lean_closure_set(v___x_611_, 1, lean_box(0));
lean_closure_set(v___x_611_, 2, v___x_602_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = l_ReaderT_instMonad___redArg(v___x_612_);
lean_inc_ref_n(v___x_613_, 6);
v___f_614_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_614_, 0, v___x_613_);
v___f_615_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_615_, 0, v___x_613_);
v___f_616_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_616_, 0, v___x_613_);
v___f_617_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_617_, 0, v___x_613_);
v___x_618_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_618_, 0, lean_box(0));
lean_closure_set(v___x_618_, 1, lean_box(0));
lean_closure_set(v___x_618_, 2, v___x_613_);
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v___f_614_);
v___x_620_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_620_, 0, lean_box(0));
lean_closure_set(v___x_620_, 1, lean_box(0));
lean_closure_set(v___x_620_, 2, v___x_613_);
v___x_621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
lean_ctor_set(v___x_621_, 2, v___f_615_);
lean_ctor_set(v___x_621_, 3, v___f_616_);
lean_ctor_set(v___x_621_, 4, v___f_617_);
v___x_622_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_622_, 0, lean_box(0));
lean_closure_set(v___x_622_, 1, lean_box(0));
lean_closure_set(v___x_622_, 2, v___x_613_);
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = l_Lean_instInhabitedExpr;
v___x_625_ = l_instInhabitedOfMonad___redArg(v___x_623_, v___x_624_);
v___x_24871__overap_626_ = lean_panic_fn_borrowed(v___x_625_, v_msg_589_);
lean_dec(v___x_625_);
v___x_627_ = lean_box(v___y_591_);
v___x_628_ = lean_apply_3(v___x_24871__overap_626_, v___y_590_, v___x_627_, v___y_592_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___boxed(lean_object* v_msg_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
uint8_t v___y_25755__boxed_633_; lean_object* v_res_634_; 
v___y_25755__boxed_633_ = lean_unbox(v___y_631_);
v_res_634_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13(v_msg_629_, v___y_630_, v___y_25755__boxed_633_, v___y_632_);
return v_res_634_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_638_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__2));
v___x_639_ = lean_unsigned_to_nat(67u);
v___x_640_ = lean_unsigned_to_nat(35u);
v___x_641_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__1));
v___x_642_ = ((lean_object*)(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0));
v___x_643_ = l_mkPanicMessageWithDecl(v___x_642_, v___x_641_, v___x_640_, v___x_639_, v___x_638_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(lean_object* v_minIndex_644_, lean_object* v___x_645_, lean_object* v___x_646_, lean_object* v_start_647_, lean_object* v_xs_648_, lean_object* v___x_649_, lean_object* v_e_650_, lean_object* v_offset_651_, lean_object* v_a_652_, uint8_t v_a_653_, lean_object* v_a_654_){
_start:
{
switch(lean_obj_tag(v_e_650_))
{
case 5:
{
lean_object* v_fn_655_; lean_object* v_arg_656_; lean_object* v___x_657_; lean_object* v_fst_658_; lean_object* v_snd_659_; lean_object* v_fst_660_; lean_object* v_snd_661_; lean_object* v___x_662_; lean_object* v_fst_663_; lean_object* v_snd_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_685_; 
v_fn_655_ = lean_ctor_get(v_e_650_, 0);
v_arg_656_ = lean_ctor_get(v_e_650_, 1);
lean_inc(v_offset_651_);
lean_inc_ref(v_fn_655_);
lean_inc_ref(v___x_649_);
lean_inc_ref(v___x_645_);
v___x_657_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_644_, v___x_645_, v___x_646_, v_start_647_, v_xs_648_, v___x_649_, v_fn_655_, v_offset_651_, v_a_652_, v_a_653_, v_a_654_);
v_fst_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_fst_658_);
v_snd_659_ = lean_ctor_get(v___x_657_, 1);
lean_inc(v_snd_659_);
lean_dec_ref(v___x_657_);
v_fst_660_ = lean_ctor_get(v_fst_658_, 0);
lean_inc(v_fst_660_);
v_snd_661_ = lean_ctor_get(v_fst_658_, 1);
lean_inc(v_snd_661_);
lean_dec(v_fst_658_);
lean_inc_ref(v_arg_656_);
v___x_662_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_644_, v___x_645_, v___x_646_, v_start_647_, v_xs_648_, v___x_649_, v_arg_656_, v_offset_651_, v_snd_661_, v_a_653_, v_snd_659_);
v_fst_663_ = lean_ctor_get(v___x_662_, 0);
v_snd_664_ = lean_ctor_get(v___x_662_, 1);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_685_ == 0)
{
v___x_666_ = v___x_662_;
v_isShared_667_ = v_isSharedCheck_685_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_snd_664_);
lean_inc(v_fst_663_);
lean_dec(v___x_662_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_685_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_fst_668_; lean_object* v_snd_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_684_; 
v_fst_668_ = lean_ctor_get(v_fst_663_, 0);
v_snd_669_ = lean_ctor_get(v_fst_663_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v_fst_663_);
if (v_isSharedCheck_684_ == 0)
{
v___x_671_ = v_fst_663_;
v_isShared_672_ = v_isSharedCheck_684_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_snd_669_);
lean_inc(v_fst_668_);
lean_dec(v_fst_663_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_684_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
uint8_t v___y_674_; uint8_t v___x_682_; 
v___x_682_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fn_655_, v_fst_660_);
if (v___x_682_ == 0)
{
v___y_674_ = v___x_682_;
goto v___jp_673_;
}
else
{
uint8_t v___x_683_; 
v___x_683_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_656_, v_fst_668_);
v___y_674_ = v___x_683_;
goto v___jp_673_;
}
v___jp_673_:
{
if (v___y_674_ == 0)
{
lean_object* v___x_675_; 
lean_del_object(v___x_671_);
lean_del_object(v___x_666_);
lean_dec_ref(v_e_650_);
v___x_675_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__7(v_fst_660_, v_fst_668_, v_snd_669_, v_a_653_, v_snd_664_);
return v___x_675_;
}
else
{
lean_object* v___x_677_; 
lean_dec(v_fst_668_);
lean_dec(v_fst_660_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v_e_650_);
v___x_677_ = v___x_671_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_e_650_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_snd_669_);
v___x_677_ = v_reuseFailAlloc_681_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_679_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_677_);
v___x_679_ = v___x_666_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_snd_664_);
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
case 6:
{
lean_object* v_binderName_686_; lean_object* v_binderType_687_; lean_object* v_body_688_; uint8_t v_binderInfo_689_; lean_object* v___x_690_; lean_object* v_fst_691_; lean_object* v_snd_692_; lean_object* v_fst_693_; lean_object* v_snd_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v_fst_698_; lean_object* v_snd_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_720_; 
v_binderName_686_ = lean_ctor_get(v_e_650_, 0);
v_binderType_687_ = lean_ctor_get(v_e_650_, 1);
v_body_688_ = lean_ctor_get(v_e_650_, 2);
v_binderInfo_689_ = lean_ctor_get_uint8(v_e_650_, sizeof(void*)*3 + 8);
lean_inc(v_offset_651_);
lean_inc_ref(v_binderType_687_);
lean_inc_ref(v___x_649_);
lean_inc_ref(v___x_645_);
v___x_690_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_644_, v___x_645_, v___x_646_, v_start_647_, v_xs_648_, v___x_649_, v_binderType_687_, v_offset_651_, v_a_652_, v_a_653_, v_a_654_);
v_fst_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_fst_691_);
v_snd_692_ = lean_ctor_get(v___x_690_, 1);
lean_inc(v_snd_692_);
lean_dec_ref(v___x_690_);
v_fst_693_ = lean_ctor_get(v_fst_691_, 0);
lean_inc(v_fst_693_);
v_snd_694_ = lean_ctor_get(v_fst_691_, 1);
lean_inc(v_snd_694_);
lean_dec(v_fst_691_);
v___x_695_ = lean_unsigned_to_nat(1u);
v___x_696_ = lean_nat_add(v_offset_651_, v___x_695_);
lean_dec(v_offset_651_);
lean_inc_ref(v_body_688_);
v___x_697_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_644_, v___x_645_, v___x_646_, v_start_647_, v_xs_648_, v___x_649_, v_body_688_, v___x_696_, v_snd_694_, v_a_653_, v_snd_692_);
v_fst_698_ = lean_ctor_get(v___x_697_, 0);
v_snd_699_ = lean_ctor_get(v___x_697_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_720_ == 0)
{
v___x_701_ = v___x_697_;
v_isShared_702_ = v_isSharedCheck_720_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_snd_699_);
lean_inc(v_fst_698_);
lean_dec(v___x_697_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_720_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v_fst_703_; lean_object* v_snd_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_719_; 
v_fst_703_ = lean_ctor_get(v_fst_698_, 0);
v_snd_704_ = lean_ctor_get(v_fst_698_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v_fst_698_);
if (v_isSharedCheck_719_ == 0)
{
v___x_706_ = v_fst_698_;
v_isShared_707_ = v_isSharedCheck_719_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_snd_704_);
lean_inc(v_fst_703_);
lean_dec(v_fst_698_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_719_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
uint8_t v___y_709_; uint8_t v___x_717_; 
v___x_717_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_687_, v_fst_693_);
if (v___x_717_ == 0)
{
v___y_709_ = v___x_717_;
goto v___jp_708_;
}
else
{
uint8_t v___x_718_; 
v___x_718_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_688_, v_fst_703_);
v___y_709_ = v___x_718_;
goto v___jp_708_;
}
v___jp_708_:
{
if (v___y_709_ == 0)
{
lean_object* v___x_710_; 
lean_inc(v_binderName_686_);
lean_del_object(v___x_706_);
lean_del_object(v___x_701_);
lean_dec_ref(v_e_650_);
v___x_710_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__8(v_binderName_686_, v_binderInfo_689_, v_fst_693_, v_fst_703_, v_snd_704_, v_a_653_, v_snd_699_);
return v___x_710_;
}
else
{
lean_object* v___x_712_; 
lean_dec(v_fst_703_);
lean_dec(v_fst_693_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v_e_650_);
v___x_712_ = v___x_706_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_e_650_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_snd_704_);
v___x_712_ = v_reuseFailAlloc_716_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_714_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_712_);
v___x_714_ = v___x_701_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_snd_699_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
}
}
}
case 7:
{
lean_object* v_binderName_721_; lean_object* v_binderType_722_; lean_object* v_body_723_; uint8_t v_binderInfo_724_; lean_object* v___x_725_; lean_object* v_fst_726_; lean_object* v_snd_727_; lean_object* v_fst_728_; lean_object* v_snd_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v_fst_733_; lean_object* v_snd_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_755_; 
v_binderName_721_ = lean_ctor_get(v_e_650_, 0);
v_binderType_722_ = lean_ctor_get(v_e_650_, 1);
v_body_723_ = lean_ctor_get(v_e_650_, 2);
v_binderInfo_724_ = lean_ctor_get_uint8(v_e_650_, sizeof(void*)*3 + 8);
lean_inc(v_offset_651_);
lean_inc_ref(v_binderType_722_);
lean_inc_ref(v___x_649_);
lean_inc_ref(v___x_645_);
v___x_725_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_644_, v___x_645_, v___x_646_, v_start_647_, v_xs_648_, v___x_649_, v_binderType_722_, v_offset_651_, v_a_652_, v_a_653_, v_a_654_);
v_fst_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_fst_726_);
v_snd_727_ = lean_ctor_get(v___x_725_, 1);
lean_inc(v_snd_727_);
lean_dec_ref(v___x_725_);
v_fst_728_ = lean_ctor_get(v_fst_726_, 0);
lean_inc(v_fst_728_);
v_snd_729_ = lean_ctor_get(v_fst_726_, 1);
lean_inc(v_snd_729_);
lean_dec(v_fst_726_);
v___x_730_ = lean_unsigned_to_nat(1u);
v___x_731_ = lean_nat_add(v_offset_651_, v___x_730_);
lean_dec(v_offset_651_);
lean_inc_ref(v_body_723_);
v___x_732_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_644_, v___x_645_, v___x_646_, v_start_647_, v_xs_648_, v___x_649_, v_body_723_, v___x_731_, v_snd_729_, v_a_653_, v_snd_727_);
v_fst_733_ = lean_ctor_get(v___x_732_, 0);
v_snd_734_ = lean_ctor_get(v___x_732_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_755_ == 0)
{
v___x_736_ = v___x_732_;
v_isShared_737_ = v_isSharedCheck_755_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_snd_734_);
lean_inc(v_fst_733_);
lean_dec(v___x_732_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_755_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v_fst_738_; lean_object* v_snd_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_754_; 
v_fst_738_ = lean_ctor_get(v_fst_733_, 0);
v_snd_739_ = lean_ctor_get(v_fst_733_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v_fst_733_);
if (v_isSharedCheck_754_ == 0)
{
v___x_741_ = v_fst_733_;
v_isShared_742_ = v_isSharedCheck_754_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_snd_739_);
lean_inc(v_fst_738_);
lean_dec(v_fst_733_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_754_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
uint8_t v___y_744_; uint8_t v___x_752_; 
v___x_752_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_722_, v_fst_728_);
if (v___x_752_ == 0)
{
v___y_744_ = v___x_752_;
goto v___jp_743_;
}
else
{
uint8_t v___x_753_; 
v___x_753_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_723_, v_fst_738_);
v___y_744_ = v___x_753_;
goto v___jp_743_;
}
v___jp_743_:
{
if (v___y_744_ == 0)
{
lean_object* v___x_745_; 
lean_inc(v_binderName_721_);
lean_del_object(v___x_741_);
lean_del_object(v___x_736_);
lean_dec_ref(v_e_650_);
v___x_745_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__9(v_binderName_721_, v_binderInfo_724_, v_fst_728_, v_fst_738_, v_snd_739_, v_a_653_, v_snd_734_);
return v___x_745_;
}
else
{
lean_object* v___x_747_; 
lean_dec(v_fst_738_);
lean_dec(v_fst_728_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v_e_650_);
v___x_747_ = v___x_741_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_e_650_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_snd_739_);
v___x_747_ = v_reuseFailAlloc_751_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_749_; 
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_747_);
v___x_749_ = v___x_736_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_snd_734_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
}
}
case 8:
{
lean_object* v_declName_756_; lean_object* v_type_757_; lean_object* v_value_758_; lean_object* v_body_759_; uint8_t v_nondep_760_; lean_object* v___x_761_; lean_object* v_fst_762_; lean_object* v_snd_763_; lean_object* v_fst_764_; lean_object* v_snd_765_; lean_object* v___x_766_; lean_object* v_fst_767_; lean_object* v_snd_768_; lean_object* v_fst_769_; lean_object* v_snd_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v_fst_774_; lean_object* v_snd_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_798_; 
v_declName_756_ = lean_ctor_get(v_e_650_, 0);
v_type_757_ = lean_ctor_get(v_e_650_, 1);
v_value_758_ = lean_ctor_get(v_e_650_, 2);
v_body_759_ = lean_ctor_get(v_e_650_, 3);
v_nondep_760_ = lean_ctor_get_uint8(v_e_650_, sizeof(void*)*4 + 8);
lean_inc_n(v_offset_651_, 2);
lean_inc_ref(v_type_757_);
lean_inc_ref_n(v___x_649_, 2);
lean_inc_ref_n(v___x_645_, 2);
v___x_761_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_644_, v___x_645_, v___x_646_, v_start_647_, v_xs_648_, v___x_649_, v_type_757_, v_offset_651_, v_a_652_, v_a_653_, v_a_654_);
v_fst_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_fst_762_);
v_snd_763_ = lean_ctor_get(v___x_761_, 1);
lean_inc(v_snd_763_);
lean_dec_ref(v___x_761_);
v_fst_764_ = lean_ctor_get(v_fst_762_, 0);
lean_inc(v_fst_764_);
v_snd_765_ = lean_ctor_get(v_fst_762_, 1);
lean_inc(v_snd_765_);
lean_dec(v_fst_762_);
lean_inc_ref(v_value_758_);
v___x_766_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_644_, v___x_645_, v___x_646_, v_start_647_, v_xs_648_, v___x_649_, v_value_758_, v_offset_651_, v_snd_765_, v_a_653_, v_snd_763_);
v_fst_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_fst_767_);
v_snd_768_ = lean_ctor_get(v___x_766_, 1);
lean_inc(v_snd_768_);
lean_dec_ref(v___x_766_);
v_fst_769_ = lean_ctor_get(v_fst_767_, 0);
lean_inc(v_fst_769_);
v_snd_770_ = lean_ctor_get(v_fst_767_, 1);
lean_inc(v_snd_770_);
lean_dec(v_fst_767_);
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = lean_nat_add(v_offset_651_, v___x_771_);
lean_dec(v_offset_651_);
lean_inc_ref(v_body_759_);
v___x_773_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_644_, v___x_645_, v___x_646_, v_start_647_, v_xs_648_, v___x_649_, v_body_759_, v___x_772_, v_snd_770_, v_a_653_, v_snd_768_);
v_fst_774_ = lean_ctor_get(v___x_773_, 0);
v_snd_775_ = lean_ctor_get(v___x_773_, 1);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_798_ == 0)
{
v___x_777_ = v___x_773_;
v_isShared_778_ = v_isSharedCheck_798_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_snd_775_);
lean_inc(v_fst_774_);
lean_dec(v___x_773_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_798_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v_fst_779_; lean_object* v_snd_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_797_; 
v_fst_779_ = lean_ctor_get(v_fst_774_, 0);
v_snd_780_ = lean_ctor_get(v_fst_774_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v_fst_774_);
if (v_isSharedCheck_797_ == 0)
{
v___x_782_ = v_fst_774_;
v_isShared_783_ = v_isSharedCheck_797_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_snd_780_);
lean_inc(v_fst_779_);
lean_dec(v_fst_774_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_797_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
uint8_t v___y_785_; uint8_t v___x_795_; 
v___x_795_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_type_757_, v_fst_764_);
if (v___x_795_ == 0)
{
v___y_785_ = v___x_795_;
goto v___jp_784_;
}
else
{
uint8_t v___x_796_; 
v___x_796_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_value_758_, v_fst_769_);
v___y_785_ = v___x_796_;
goto v___jp_784_;
}
v___jp_784_:
{
if (v___y_785_ == 0)
{
lean_object* v___x_786_; 
lean_inc(v_declName_756_);
lean_del_object(v___x_782_);
lean_del_object(v___x_777_);
lean_dec_ref(v_e_650_);
v___x_786_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10(v_declName_756_, v_fst_764_, v_fst_769_, v_fst_779_, v_nondep_760_, v_snd_780_, v_a_653_, v_snd_775_);
return v___x_786_;
}
else
{
uint8_t v___x_787_; 
v___x_787_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_759_, v_fst_779_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; 
lean_inc(v_declName_756_);
lean_del_object(v___x_782_);
lean_del_object(v___x_777_);
lean_dec_ref(v_e_650_);
v___x_788_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10(v_declName_756_, v_fst_764_, v_fst_769_, v_fst_779_, v_nondep_760_, v_snd_780_, v_a_653_, v_snd_775_);
return v___x_788_;
}
else
{
lean_object* v___x_790_; 
lean_dec(v_fst_779_);
lean_dec(v_fst_769_);
lean_dec(v_fst_764_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v_e_650_);
v___x_790_ = v___x_782_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_e_650_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_snd_780_);
v___x_790_ = v_reuseFailAlloc_794_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_792_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_790_);
v___x_792_ = v___x_777_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_snd_775_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
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
lean_object* v_data_799_; lean_object* v_expr_800_; lean_object* v___x_801_; lean_object* v_fst_802_; lean_object* v_snd_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_821_; 
v_data_799_ = lean_ctor_get(v_e_650_, 0);
v_expr_800_ = lean_ctor_get(v_e_650_, 1);
lean_inc_ref(v_expr_800_);
v___x_801_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_644_, v___x_645_, v___x_646_, v_start_647_, v_xs_648_, v___x_649_, v_expr_800_, v_offset_651_, v_a_652_, v_a_653_, v_a_654_);
v_fst_802_ = lean_ctor_get(v___x_801_, 0);
v_snd_803_ = lean_ctor_get(v___x_801_, 1);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_821_ == 0)
{
v___x_805_ = v___x_801_;
v_isShared_806_ = v_isSharedCheck_821_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_snd_803_);
lean_inc(v_fst_802_);
lean_dec(v___x_801_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_821_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v_fst_807_; lean_object* v_snd_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_820_; 
v_fst_807_ = lean_ctor_get(v_fst_802_, 0);
v_snd_808_ = lean_ctor_get(v_fst_802_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v_fst_802_);
if (v_isSharedCheck_820_ == 0)
{
v___x_810_ = v_fst_802_;
v_isShared_811_ = v_isSharedCheck_820_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_snd_808_);
lean_inc(v_fst_807_);
lean_dec(v_fst_802_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_820_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
uint8_t v___x_812_; 
v___x_812_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_expr_800_, v_fst_807_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; 
lean_inc(v_data_799_);
lean_del_object(v___x_810_);
lean_del_object(v___x_805_);
lean_dec_ref(v_e_650_);
v___x_813_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__11(v_data_799_, v_fst_807_, v_snd_808_, v_a_653_, v_snd_803_);
return v___x_813_;
}
else
{
lean_object* v___x_815_; 
lean_dec(v_fst_807_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v_e_650_);
v___x_815_ = v___x_810_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_e_650_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_snd_808_);
v___x_815_ = v_reuseFailAlloc_819_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_817_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_815_);
v___x_817_ = v___x_805_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_snd_803_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
}
case 11:
{
lean_object* v_typeName_822_; lean_object* v_idx_823_; lean_object* v_struct_824_; lean_object* v___x_825_; lean_object* v_fst_826_; lean_object* v_snd_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_845_; 
v_typeName_822_ = lean_ctor_get(v_e_650_, 0);
v_idx_823_ = lean_ctor_get(v_e_650_, 1);
v_struct_824_ = lean_ctor_get(v_e_650_, 2);
lean_inc_ref(v_struct_824_);
v___x_825_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_644_, v___x_645_, v___x_646_, v_start_647_, v_xs_648_, v___x_649_, v_struct_824_, v_offset_651_, v_a_652_, v_a_653_, v_a_654_);
v_fst_826_ = lean_ctor_get(v___x_825_, 0);
v_snd_827_ = lean_ctor_get(v___x_825_, 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_845_ == 0)
{
v___x_829_ = v___x_825_;
v_isShared_830_ = v_isSharedCheck_845_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_snd_827_);
lean_inc(v_fst_826_);
lean_dec(v___x_825_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_845_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v_fst_831_; lean_object* v_snd_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_844_; 
v_fst_831_ = lean_ctor_get(v_fst_826_, 0);
v_snd_832_ = lean_ctor_get(v_fst_826_, 1);
v_isSharedCheck_844_ = !lean_is_exclusive(v_fst_826_);
if (v_isSharedCheck_844_ == 0)
{
v___x_834_ = v_fst_826_;
v_isShared_835_ = v_isSharedCheck_844_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_snd_832_);
lean_inc(v_fst_831_);
lean_dec(v_fst_826_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_844_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
uint8_t v___x_836_; 
v___x_836_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_824_, v_fst_831_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; 
lean_inc(v_idx_823_);
lean_inc(v_typeName_822_);
lean_del_object(v___x_834_);
lean_del_object(v___x_829_);
lean_dec_ref(v_e_650_);
v___x_837_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__12(v_typeName_822_, v_idx_823_, v_fst_831_, v_snd_832_, v_a_653_, v_snd_827_);
return v___x_837_;
}
else
{
lean_object* v___x_839_; 
lean_dec(v_fst_831_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v_e_650_);
v___x_839_ = v___x_834_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_e_650_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_snd_832_);
v___x_839_ = v_reuseFailAlloc_843_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_841_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_839_);
v___x_841_ = v___x_829_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_snd_827_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec(v_offset_651_);
lean_dec_ref(v_e_650_);
lean_dec_ref(v___x_649_);
lean_dec_ref(v___x_645_);
v___x_846_ = lean_obj_once(&l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3, &l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3_once, _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3);
v___x_847_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13(v___x_846_, v_a_652_, v_a_653_, v_a_654_);
return v___x_847_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(lean_object* v_minIndex_848_, lean_object* v___x_849_, lean_object* v___x_850_, lean_object* v_start_851_, lean_object* v_xs_852_, lean_object* v___x_853_, lean_object* v_e_854_, lean_object* v_offset_855_, lean_object* v_a_856_, uint8_t v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_key_859_; lean_object* v_snd_861_; lean_object* v___y_875_; lean_object* v___y_880_; lean_object* v___x_885_; 
lean_inc(v_offset_855_);
lean_inc_ref(v_e_854_);
v_key_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_859_, 0, v_e_854_);
lean_ctor_set(v_key_859_, 1, v_offset_855_);
v___x_885_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg(v_a_856_, v_key_859_);
if (lean_obj_tag(v___x_885_) == 1)
{
lean_object* v_val_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
lean_dec_ref(v_key_859_);
lean_dec(v_offset_855_);
lean_dec_ref(v_e_854_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_849_);
v_val_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_val_886_);
lean_dec_ref(v___x_885_);
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v_val_886_);
lean_ctor_set(v___x_887_, 1, v_a_856_);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v_a_858_);
return v___x_888_;
}
else
{
lean_dec(v___x_885_);
switch(lean_obj_tag(v_e_854_))
{
case 1:
{
lean_object* v_fvarId_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_849_);
v_fvarId_889_ = lean_ctor_get(v_e_854_, 0);
v___x_890_ = lean_unsigned_to_nat(0u);
v___x_891_ = lean_unsigned_to_nat(1u);
v___x_892_ = lean_nat_sub(v___x_850_, v___x_891_);
v___x_893_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_851_, v_xs_852_, v_fvarId_889_, v___x_890_, v___x_892_);
if (lean_obj_tag(v___x_893_) == 1)
{
lean_object* v_val_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v_fst_897_; lean_object* v_snd_898_; lean_object* v___x_899_; 
lean_dec_ref(v_e_854_);
v_val_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_val_894_);
lean_dec_ref(v___x_893_);
v___x_895_ = lean_nat_add(v_offset_855_, v_val_894_);
lean_dec(v_val_894_);
lean_dec(v_offset_855_);
v___x_896_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v___x_895_, v_a_858_);
v_fst_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_fst_897_);
v_snd_898_ = lean_ctor_get(v___x_896_, 1);
lean_inc(v_snd_898_);
lean_dec_ref(v___x_896_);
v___x_899_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_859_, v_fst_897_, v_a_856_, v_a_857_, v_snd_898_);
return v___x_899_;
}
else
{
lean_object* v___x_900_; 
lean_dec(v___x_893_);
lean_dec(v_offset_855_);
v___x_900_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_859_, v_e_854_, v_a_856_, v_a_857_, v_a_858_);
return v___x_900_;
}
}
case 9:
{
lean_object* v___x_901_; 
lean_dec(v_offset_855_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_849_);
v___x_901_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_859_, v_e_854_, v_a_856_, v_a_857_, v_a_858_);
return v___x_901_;
}
case 2:
{
lean_object* v___x_902_; 
lean_dec(v_offset_855_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_849_);
v___x_902_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_859_, v_e_854_, v_a_856_, v_a_857_, v_a_858_);
return v___x_902_;
}
case 0:
{
lean_object* v___x_903_; 
lean_dec(v_offset_855_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_849_);
v___x_903_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_859_, v_e_854_, v_a_856_, v_a_857_, v_a_858_);
return v___x_903_;
}
case 4:
{
lean_object* v___x_904_; 
lean_dec(v_offset_855_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_849_);
v___x_904_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_859_, v_e_854_, v_a_856_, v_a_857_, v_a_858_);
return v___x_904_;
}
case 3:
{
lean_object* v___x_905_; 
lean_dec(v_offset_855_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_849_);
v___x_905_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_859_, v_e_854_, v_a_856_, v_a_857_, v_a_858_);
return v___x_905_;
}
default: 
{
uint8_t v___x_906_; 
v___x_906_ = l_Lean_Expr_hasFVar(v_e_854_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; 
lean_dec(v_offset_855_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_849_);
v___x_907_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_859_, v_e_854_, v_a_856_, v_a_857_, v_a_858_);
return v___x_907_;
}
else
{
lean_object* v___x_908_; 
lean_inc_ref(v___x_853_);
v___x_908_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(v___x_853_, v_e_854_);
if (lean_obj_tag(v___x_908_) == 1)
{
lean_object* v_val_909_; 
v_val_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_val_909_);
lean_dec_ref(v___x_908_);
if (lean_obj_tag(v_val_909_) == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_911_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v___x_910_);
v___y_880_ = v___x_911_;
goto v___jp_879_;
}
else
{
lean_object* v_val_912_; 
v_val_912_ = lean_ctor_get(v_val_909_, 0);
lean_inc(v_val_912_);
lean_dec_ref(v_val_909_);
v___y_880_ = v_val_912_;
goto v___jp_879_;
}
}
else
{
lean_dec(v___x_908_);
v_snd_861_ = v_a_858_;
goto v___jp_860_;
}
}
}
}
}
v___jp_860_:
{
switch(lean_obj_tag(v_e_854_))
{
case 9:
{
lean_object* v___x_862_; 
lean_dec(v_offset_855_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_849_);
v___x_862_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_859_, v_e_854_, v_a_856_, v_a_857_, v_snd_861_);
return v___x_862_;
}
case 2:
{
lean_object* v___x_863_; 
lean_dec(v_offset_855_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_849_);
v___x_863_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_859_, v_e_854_, v_a_856_, v_a_857_, v_snd_861_);
return v___x_863_;
}
case 0:
{
lean_object* v___x_864_; 
lean_dec(v_offset_855_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_849_);
v___x_864_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_859_, v_e_854_, v_a_856_, v_a_857_, v_snd_861_);
return v___x_864_;
}
case 1:
{
lean_object* v___x_865_; 
lean_dec(v_offset_855_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_849_);
v___x_865_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_859_, v_e_854_, v_a_856_, v_a_857_, v_snd_861_);
return v___x_865_;
}
case 4:
{
lean_object* v___x_866_; 
lean_dec(v_offset_855_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_849_);
v___x_866_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_859_, v_e_854_, v_a_856_, v_a_857_, v_snd_861_);
return v___x_866_;
}
case 3:
{
lean_object* v___x_867_; 
lean_dec(v_offset_855_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_849_);
v___x_867_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_859_, v_e_854_, v_a_856_, v_a_857_, v_snd_861_);
return v___x_867_;
}
default: 
{
lean_object* v___x_868_; lean_object* v_fst_869_; lean_object* v_snd_870_; lean_object* v_fst_871_; lean_object* v_snd_872_; lean_object* v___x_873_; 
v___x_868_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v_minIndex_848_, v___x_849_, v___x_850_, v_start_851_, v_xs_852_, v___x_853_, v_e_854_, v_offset_855_, v_a_856_, v_a_857_, v_snd_861_);
v_fst_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_fst_869_);
v_snd_870_ = lean_ctor_get(v___x_868_, 1);
lean_inc(v_snd_870_);
lean_dec_ref(v___x_868_);
v_fst_871_ = lean_ctor_get(v_fst_869_, 0);
lean_inc(v_fst_871_);
v_snd_872_ = lean_ctor_get(v_fst_869_, 1);
lean_inc(v_snd_872_);
lean_dec(v_fst_869_);
v___x_873_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_859_, v_fst_871_, v_snd_872_, v_a_857_, v_snd_870_);
return v___x_873_;
}
}
}
v___jp_874_:
{
lean_object* v_maxIndex_876_; uint8_t v___x_877_; 
v_maxIndex_876_ = l_Lean_LocalDecl_index(v___y_875_);
lean_dec_ref(v___y_875_);
v___x_877_ = lean_nat_dec_lt(v_maxIndex_876_, v_minIndex_848_);
lean_dec(v_maxIndex_876_);
if (v___x_877_ == 0)
{
v_snd_861_ = v_a_858_;
goto v___jp_860_;
}
else
{
lean_object* v___x_878_; 
lean_dec(v_offset_855_);
lean_dec_ref(v___x_853_);
lean_dec_ref(v___x_849_);
v___x_878_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(v_key_859_, v_e_854_, v_a_856_, v_a_857_, v_a_858_);
return v___x_878_;
}
}
v___jp_879_:
{
lean_object* v___x_881_; 
lean_inc_ref(v___x_849_);
v___x_881_ = lean_local_ctx_find(v___x_849_, v___y_880_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_883_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v___x_882_);
v___y_875_ = v___x_883_;
goto v___jp_874_;
}
else
{
lean_object* v_val_884_; 
v_val_884_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_val_884_);
lean_dec_ref(v___x_881_);
v___y_875_ = v_val_884_;
goto v___jp_874_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6___boxed(lean_object* v_minIndex_913_, lean_object* v___x_914_, lean_object* v___x_915_, lean_object* v_start_916_, lean_object* v_xs_917_, lean_object* v___x_918_, lean_object* v_e_919_, lean_object* v_offset_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
uint8_t v_a_boxed_924_; lean_object* v_res_925_; 
v_a_boxed_924_ = lean_unbox(v_a_922_);
v_res_925_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_913_, v___x_914_, v___x_915_, v_start_916_, v_xs_917_, v___x_918_, v_e_919_, v_offset_920_, v_a_921_, v_a_boxed_924_, v_a_923_);
lean_dec_ref(v_xs_917_);
lean_dec(v_start_916_);
lean_dec(v___x_915_);
lean_dec(v_minIndex_913_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___boxed(lean_object* v_minIndex_926_, lean_object* v___x_927_, lean_object* v___x_928_, lean_object* v_start_929_, lean_object* v_xs_930_, lean_object* v___x_931_, lean_object* v_e_932_, lean_object* v_offset_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
uint8_t v_a_boxed_937_; lean_object* v_res_938_; 
v_a_boxed_937_ = lean_unbox(v_a_935_);
v_res_938_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v_minIndex_926_, v___x_927_, v___x_928_, v_start_929_, v_xs_930_, v___x_931_, v_e_932_, v_offset_933_, v_a_934_, v_a_boxed_937_, v_a_936_);
lean_dec_ref(v_xs_930_);
lean_dec(v_start_929_);
lean_dec(v___x_928_);
lean_dec(v_minIndex_926_);
return v_res_938_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0(void){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(lean_box(0));
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___redArg(lean_object* v_e_940_, lean_object* v_start_941_, lean_object* v_xs_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = l_Lean_Expr_hasFVar(v_e_940_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; 
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v_e_940_);
return v___x_947_;
}
else
{
lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_948_ = lean_array_get_size(v_xs_942_);
v___x_949_ = lean_nat_dec_lt(v_start_941_, v___x_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v_e_940_);
return v___x_950_;
}
else
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v_share_953_; lean_object* v_maxFVar_954_; lean_object* v_proofInstInfo_955_; lean_object* v_inferType_956_; lean_object* v_getLevel_957_; lean_object* v_congrInfo_958_; lean_object* v_defEqI_959_; lean_object* v_extensions_960_; lean_object* v_issues_961_; lean_object* v_canon_962_; uint8_t v_debug_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_1047_; 
v___x_951_ = lean_st_ref_get(v_a_943_);
v___x_952_ = lean_st_ref_take(v_a_943_);
v_share_953_ = lean_ctor_get(v___x_952_, 0);
v_maxFVar_954_ = lean_ctor_get(v___x_952_, 1);
v_proofInstInfo_955_ = lean_ctor_get(v___x_952_, 2);
v_inferType_956_ = lean_ctor_get(v___x_952_, 3);
v_getLevel_957_ = lean_ctor_get(v___x_952_, 4);
v_congrInfo_958_ = lean_ctor_get(v___x_952_, 5);
v_defEqI_959_ = lean_ctor_get(v___x_952_, 6);
v_extensions_960_ = lean_ctor_get(v___x_952_, 7);
v_issues_961_ = lean_ctor_get(v___x_952_, 8);
v_canon_962_ = lean_ctor_get(v___x_952_, 9);
v_debug_963_ = lean_ctor_get_uint8(v___x_952_, sizeof(void*)*10);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_965_ = v___x_952_;
v_isShared_966_ = v_isSharedCheck_1047_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_canon_962_);
lean_inc(v_issues_961_);
lean_inc(v_extensions_960_);
lean_inc(v_defEqI_959_);
lean_inc(v_congrInfo_958_);
lean_inc(v_getLevel_957_);
lean_inc(v_inferType_956_);
lean_inc(v_proofInstInfo_955_);
lean_inc(v_maxFVar_954_);
lean_inc(v_share_953_);
lean_dec(v___x_952_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_1047_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_967_ = lean_obj_once(&l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0, &l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0_once, _init_l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_967_);
v___x_969_ = v___x_965_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_maxFVar_954_);
lean_ctor_set(v_reuseFailAlloc_1046_, 2, v_proofInstInfo_955_);
lean_ctor_set(v_reuseFailAlloc_1046_, 3, v_inferType_956_);
lean_ctor_set(v_reuseFailAlloc_1046_, 4, v_getLevel_957_);
lean_ctor_set(v_reuseFailAlloc_1046_, 5, v_congrInfo_958_);
lean_ctor_set(v_reuseFailAlloc_1046_, 6, v_defEqI_959_);
lean_ctor_set(v_reuseFailAlloc_1046_, 7, v_extensions_960_);
lean_ctor_set(v_reuseFailAlloc_1046_, 8, v_issues_961_);
lean_ctor_set(v_reuseFailAlloc_1046_, 9, v_canon_962_);
lean_ctor_set_uint8(v_reuseFailAlloc_1046_, sizeof(void*)*10, v_debug_963_);
v___x_969_ = v_reuseFailAlloc_1046_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v_fst_973_; lean_object* v_snd_974_; lean_object* v_lctx_996_; lean_object* v_maxFVar_997_; uint8_t v_debug_998_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v_snd_1002_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1024_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_970_ = lean_st_ref_set(v_a_943_, v___x_969_);
v___x_971_ = lean_st_ref_get(v_a_943_);
v_lctx_996_ = lean_ctor_get(v_a_944_, 2);
v_maxFVar_997_ = lean_ctor_get(v___x_951_, 1);
lean_inc_ref(v_maxFVar_997_);
lean_dec(v___x_951_);
v_debug_998_ = lean_ctor_get_uint8(v___x_971_, sizeof(void*)*10);
lean_dec(v___x_971_);
v___x_1040_ = lean_array_fget_borrowed(v_xs_942_, v_start_941_);
v___x_1041_ = l_Lean_Expr_fvarId_x21(v___x_1040_);
lean_inc_ref(v_lctx_996_);
v___x_1042_ = lean_local_ctx_find(v_lctx_996_, v___x_1041_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1044_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v___x_1043_);
v___y_1024_ = v___x_1044_;
goto v___jp_1023_;
}
else
{
lean_object* v_val_1045_; 
v_val_1045_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_val_1045_);
lean_dec_ref(v___x_1042_);
v___y_1024_ = v_val_1045_;
goto v___jp_1023_;
}
v___jp_972_:
{
lean_object* v___x_975_; lean_object* v_maxFVar_976_; lean_object* v_proofInstInfo_977_; lean_object* v_inferType_978_; lean_object* v_getLevel_979_; lean_object* v_congrInfo_980_; lean_object* v_defEqI_981_; lean_object* v_extensions_982_; lean_object* v_issues_983_; lean_object* v_canon_984_; uint8_t v_debug_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_994_; 
v___x_975_ = lean_st_ref_take(v_a_943_);
v_maxFVar_976_ = lean_ctor_get(v___x_975_, 1);
v_proofInstInfo_977_ = lean_ctor_get(v___x_975_, 2);
v_inferType_978_ = lean_ctor_get(v___x_975_, 3);
v_getLevel_979_ = lean_ctor_get(v___x_975_, 4);
v_congrInfo_980_ = lean_ctor_get(v___x_975_, 5);
v_defEqI_981_ = lean_ctor_get(v___x_975_, 6);
v_extensions_982_ = lean_ctor_get(v___x_975_, 7);
v_issues_983_ = lean_ctor_get(v___x_975_, 8);
v_canon_984_ = lean_ctor_get(v___x_975_, 9);
v_debug_985_ = lean_ctor_get_uint8(v___x_975_, sizeof(void*)*10);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; 
v_unused_995_ = lean_ctor_get(v___x_975_, 0);
lean_dec(v_unused_995_);
v___x_987_ = v___x_975_;
v_isShared_988_ = v_isSharedCheck_994_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_canon_984_);
lean_inc(v_issues_983_);
lean_inc(v_extensions_982_);
lean_inc(v_defEqI_981_);
lean_inc(v_congrInfo_980_);
lean_inc(v_getLevel_979_);
lean_inc(v_inferType_978_);
lean_inc(v_proofInstInfo_977_);
lean_inc(v_maxFVar_976_);
lean_dec(v___x_975_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_994_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v_snd_974_);
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_snd_974_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_maxFVar_976_);
lean_ctor_set(v_reuseFailAlloc_993_, 2, v_proofInstInfo_977_);
lean_ctor_set(v_reuseFailAlloc_993_, 3, v_inferType_978_);
lean_ctor_set(v_reuseFailAlloc_993_, 4, v_getLevel_979_);
lean_ctor_set(v_reuseFailAlloc_993_, 5, v_congrInfo_980_);
lean_ctor_set(v_reuseFailAlloc_993_, 6, v_defEqI_981_);
lean_ctor_set(v_reuseFailAlloc_993_, 7, v_extensions_982_);
lean_ctor_set(v_reuseFailAlloc_993_, 8, v_issues_983_);
lean_ctor_set(v_reuseFailAlloc_993_, 9, v_canon_984_);
lean_ctor_set_uint8(v_reuseFailAlloc_993_, sizeof(void*)*10, v_debug_985_);
v___x_990_ = v_reuseFailAlloc_993_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_st_ref_set(v_a_943_, v___x_990_);
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v_fst_973_);
return v___x_992_;
}
}
}
v___jp_999_:
{
switch(lean_obj_tag(v_e_940_))
{
case 9:
{
lean_dec(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v_maxFVar_997_);
v_fst_973_ = v_e_940_;
v_snd_974_ = v_snd_1002_;
goto v___jp_972_;
}
case 2:
{
lean_dec(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v_maxFVar_997_);
v_fst_973_ = v_e_940_;
v_snd_974_ = v_snd_1002_;
goto v___jp_972_;
}
case 0:
{
lean_dec(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v_maxFVar_997_);
v_fst_973_ = v_e_940_;
v_snd_974_ = v_snd_1002_;
goto v___jp_972_;
}
case 1:
{
lean_dec(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v_maxFVar_997_);
v_fst_973_ = v_e_940_;
v_snd_974_ = v_snd_1002_;
goto v___jp_972_;
}
case 4:
{
lean_dec(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v_maxFVar_997_);
v_fst_973_ = v_e_940_;
v_snd_974_ = v_snd_1002_;
goto v___jp_972_;
}
case 3:
{
lean_dec(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v_maxFVar_997_);
v_fst_973_ = v_e_940_;
v_snd_974_ = v_snd_1002_;
goto v___jp_972_;
}
default: 
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v_fst_1006_; lean_object* v_snd_1007_; lean_object* v_fst_1008_; 
v___x_1003_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0);
lean_inc(v___y_1000_);
v___x_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___y_1000_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
lean_inc_ref(v_lctx_996_);
v___x_1005_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v___y_1001_, v_lctx_996_, v___x_948_, v_start_941_, v_xs_942_, v_maxFVar_997_, v_e_940_, v___y_1000_, v___x_1004_, v_debug_998_, v_snd_1002_);
lean_dec(v___y_1001_);
v_fst_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_fst_1006_);
v_snd_1007_ = lean_ctor_get(v___x_1005_, 1);
lean_inc(v_snd_1007_);
lean_dec_ref(v___x_1005_);
v_fst_1008_ = lean_ctor_get(v_fst_1006_, 0);
lean_inc(v_fst_1008_);
lean_dec(v_fst_1006_);
v_fst_973_ = v_fst_1008_;
v_snd_974_ = v_snd_1007_;
goto v___jp_972_;
}
}
}
v___jp_1009_:
{
lean_object* v_maxIndex_1013_; uint8_t v___x_1014_; 
v_maxIndex_1013_ = l_Lean_LocalDecl_index(v___y_1012_);
lean_dec_ref(v___y_1012_);
v___x_1014_ = lean_nat_dec_lt(v_maxIndex_1013_, v___y_1011_);
lean_dec(v_maxIndex_1013_);
if (v___x_1014_ == 0)
{
v___y_1000_ = v___y_1010_;
v___y_1001_ = v___y_1011_;
v_snd_1002_ = v_share_953_;
goto v___jp_999_;
}
else
{
lean_dec(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v_maxFVar_997_);
v_fst_973_ = v_e_940_;
v_snd_974_ = v_share_953_;
goto v___jp_972_;
}
}
v___jp_1015_:
{
lean_object* v___x_1019_; 
lean_inc_ref(v_lctx_996_);
v___x_1019_ = lean_local_ctx_find(v_lctx_996_, v___y_1018_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1021_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v___x_1020_);
v___y_1010_ = v___y_1016_;
v___y_1011_ = v___y_1017_;
v___y_1012_ = v___x_1021_;
goto v___jp_1009_;
}
else
{
lean_object* v_val_1022_; 
v_val_1022_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_val_1022_);
lean_dec_ref(v___x_1019_);
v___y_1010_ = v___y_1016_;
v___y_1011_ = v___y_1017_;
v___y_1012_ = v_val_1022_;
goto v___jp_1009_;
}
}
v___jp_1023_:
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_unsigned_to_nat(0u);
switch(lean_obj_tag(v_e_940_))
{
case 1:
{
lean_object* v_fvarId_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
lean_dec_ref(v___y_1024_);
lean_dec_ref(v_maxFVar_997_);
v_fvarId_1026_ = lean_ctor_get(v_e_940_, 0);
v___x_1027_ = lean_unsigned_to_nat(1u);
v___x_1028_ = lean_nat_sub(v___x_948_, v___x_1027_);
v___x_1029_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_941_, v_xs_942_, v_fvarId_1026_, v___x_1025_, v___x_1028_);
if (lean_obj_tag(v___x_1029_) == 1)
{
lean_object* v_val_1030_; lean_object* v___x_1031_; lean_object* v_fst_1032_; lean_object* v_snd_1033_; 
lean_dec_ref(v_e_940_);
v_val_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_val_1030_);
lean_dec_ref(v___x_1029_);
v___x_1031_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_val_1030_, v_share_953_);
v_fst_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_fst_1032_);
v_snd_1033_ = lean_ctor_get(v___x_1031_, 1);
lean_inc(v_snd_1033_);
lean_dec_ref(v___x_1031_);
v_fst_973_ = v_fst_1032_;
v_snd_974_ = v_snd_1033_;
goto v___jp_972_;
}
else
{
lean_dec(v___x_1029_);
v_fst_973_ = v_e_940_;
v_snd_974_ = v_share_953_;
goto v___jp_972_;
}
}
case 9:
{
lean_dec_ref(v___y_1024_);
lean_dec_ref(v_maxFVar_997_);
v_fst_973_ = v_e_940_;
v_snd_974_ = v_share_953_;
goto v___jp_972_;
}
case 2:
{
lean_dec_ref(v___y_1024_);
lean_dec_ref(v_maxFVar_997_);
v_fst_973_ = v_e_940_;
v_snd_974_ = v_share_953_;
goto v___jp_972_;
}
case 0:
{
lean_dec_ref(v___y_1024_);
lean_dec_ref(v_maxFVar_997_);
v_fst_973_ = v_e_940_;
v_snd_974_ = v_share_953_;
goto v___jp_972_;
}
case 4:
{
lean_dec_ref(v___y_1024_);
lean_dec_ref(v_maxFVar_997_);
v_fst_973_ = v_e_940_;
v_snd_974_ = v_share_953_;
goto v___jp_972_;
}
case 3:
{
lean_dec_ref(v___y_1024_);
lean_dec_ref(v_maxFVar_997_);
v_fst_973_ = v_e_940_;
v_snd_974_ = v_share_953_;
goto v___jp_972_;
}
default: 
{
if (v___x_946_ == 0)
{
lean_dec_ref(v___y_1024_);
lean_dec_ref(v_maxFVar_997_);
v_fst_973_ = v_e_940_;
v_snd_974_ = v_share_953_;
goto v___jp_972_;
}
else
{
lean_object* v_minIndex_1034_; lean_object* v___x_1035_; 
v_minIndex_1034_ = l_Lean_LocalDecl_index(v___y_1024_);
lean_dec_ref(v___y_1024_);
lean_inc_ref(v_maxFVar_997_);
v___x_1035_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(v_maxFVar_997_, v_e_940_);
if (lean_obj_tag(v___x_1035_) == 1)
{
lean_object* v_val_1036_; 
v_val_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_val_1036_);
lean_dec_ref(v___x_1035_);
if (lean_obj_tag(v_val_1036_) == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_obj_once(&l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3, &l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once, _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
v___x_1038_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v___x_1037_);
v___y_1016_ = v___x_1025_;
v___y_1017_ = v_minIndex_1034_;
v___y_1018_ = v___x_1038_;
goto v___jp_1015_;
}
else
{
lean_object* v_val_1039_; 
v_val_1039_ = lean_ctor_get(v_val_1036_, 0);
lean_inc(v_val_1039_);
lean_dec_ref(v_val_1036_);
v___y_1016_ = v___x_1025_;
v___y_1017_ = v_minIndex_1034_;
v___y_1018_ = v_val_1039_;
goto v___jp_1015_;
}
}
else
{
lean_dec(v___x_1035_);
v___y_1000_ = v___x_1025_;
v___y_1001_ = v_minIndex_1034_;
v_snd_1002_ = v_share_953_;
goto v___jp_999_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___redArg___boxed(lean_object* v_e_1048_, lean_object* v_start_1049_, lean_object* v_xs_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v_e_1048_, v_start_1049_, v_xs_1050_, v_a_1051_, v_a_1052_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_xs_1050_);
lean_dec(v_start_1049_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange(lean_object* v_e_1055_, lean_object* v_start_1056_, lean_object* v_xs_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v_e_1055_, v_start_1056_, v_xs_1057_, v_a_1059_, v_a_1060_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVarsRange___boxed(lean_object* v_e_1066_, lean_object* v_start_1067_, lean_object* v_xs_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_Meta_Sym_abstractFVarsRange(v_e_1066_, v_start_1067_, v_xs_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec_ref(v_xs_1068_);
lean_dec(v_start_1067_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(lean_object* v_00_u03b2_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(v_x_1078_, v_x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___boxed(lean_object* v_00_u03b2_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(v_00_u03b2_1081_, v_x_1082_, v_x_1083_);
lean_dec_ref(v_x_1083_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3(lean_object* v_00_u03b2_1085_, lean_object* v_x_1086_, size_t v_x_1087_, lean_object* v_x_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(v_x_1086_, v_x_1087_, v_x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___boxed(lean_object* v_00_u03b2_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_){
_start:
{
size_t v_x_26641__boxed_1094_; lean_object* v_res_1095_; 
v_x_26641__boxed_1094_ = lean_unbox_usize(v_x_1092_);
lean_dec(v_x_1092_);
v_res_1095_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3(v_00_u03b2_1090_, v_x_1091_, v_x_26641__boxed_1094_, v_x_1093_);
lean_dec_ref(v_x_1093_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5(lean_object* v_00_u03b2_1096_, lean_object* v_keys_1097_, lean_object* v_vals_1098_, lean_object* v_heq_1099_, lean_object* v_i_1100_, lean_object* v_k_1101_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg(v_keys_1097_, v_vals_1098_, v_i_1100_, v_k_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1103_, lean_object* v_keys_1104_, lean_object* v_vals_1105_, lean_object* v_heq_1106_, lean_object* v_i_1107_, lean_object* v_k_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5(v_00_u03b2_1103_, v_keys_1104_, v_vals_1105_, v_heq_1106_, v_i_1107_, v_k_1108_);
lean_dec_ref(v_k_1108_);
lean_dec_ref(v_vals_1105_);
lean_dec_ref(v_keys_1104_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_1110_, lean_object* v_m_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg(v_m_1111_, v_a_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1114_, lean_object* v_m_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8(v_00_u03b2_1114_, v_m_1115_, v_a_1116_);
lean_dec_ref(v_a_1116_);
lean_dec_ref(v_m_1115_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16(lean_object* v_00_u03b2_1118_, lean_object* v_a_1119_, lean_object* v_x_1120_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___redArg(v_a_1119_, v_x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___boxed(lean_object* v_00_u03b2_1122_, lean_object* v_a_1123_, lean_object* v_x_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16(v_00_u03b2_1122_, v_a_1123_, v_x_1124_);
lean_dec(v_x_1124_);
lean_dec_ref(v_a_1123_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars___redArg(lean_object* v_e_1126_, lean_object* v_xs_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v_e_1126_, v___x_1131_, v_xs_1127_, v_a_1128_, v_a_1129_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars___redArg___boxed(lean_object* v_e_1133_, lean_object* v_xs_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_Meta_Sym_abstractFVars___redArg(v_e_1133_, v_xs_1134_, v_a_1135_, v_a_1136_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec_ref(v_xs_1134_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars(lean_object* v_e_1139_, lean_object* v_xs_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = lean_unsigned_to_nat(0u);
v___x_1149_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v_e_1139_, v___x_1148_, v_xs_1140_, v_a_1142_, v_a_1143_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_abstractFVars___boxed(lean_object* v_e_1150_, lean_object* v_xs_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Meta_Sym_abstractFVars(v_e_1150_, v_xs_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec_ref(v_xs_1151_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(lean_object* v_x_1160_, uint8_t v_bi_1161_, lean_object* v_t_1162_, lean_object* v_b_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v___y_1172_; lean_object* v___x_1175_; uint8_t v_debug_1176_; 
v___x_1175_ = lean_st_ref_get(v___y_1165_);
v_debug_1176_ = lean_ctor_get_uint8(v___x_1175_, sizeof(void*)*10);
lean_dec(v___x_1175_);
if (v_debug_1176_ == 0)
{
v___y_1172_ = v___y_1165_;
goto v___jp_1171_;
}
else
{
lean_object* v___x_1177_; 
lean_inc_ref(v_t_1162_);
v___x_1177_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1162_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v___x_1178_; 
lean_dec_ref(v___x_1177_);
lean_inc_ref(v_b_1163_);
v___x_1178_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_dec_ref(v___x_1178_);
v___y_1172_ = v___y_1165_;
goto v___jp_1171_;
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec_ref(v_b_1163_);
lean_dec_ref(v_t_1162_);
lean_dec(v_x_1160_);
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec_ref(v_b_1163_);
lean_dec_ref(v_t_1162_);
lean_dec(v_x_1160_);
v_a_1187_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1177_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1177_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
v___jp_1171_:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = l_Lean_Expr_lam___override(v_x_1160_, v_t_1162_, v_b_1163_, v_bi_1161_);
v___x_1174_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1173_, v___y_1172_);
return v___x_1174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0___boxed(lean_object* v_x_1195_, lean_object* v_bi_1196_, lean_object* v_t_1197_, lean_object* v_b_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
uint8_t v_bi_boxed_1206_; lean_object* v_res_1207_; 
v_bi_boxed_1206_ = lean_unbox(v_bi_1196_);
v_res_1207_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v_x_1195_, v_bi_boxed_1206_, v_t_1197_, v_b_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(lean_object* v_xs_1208_, lean_object* v_i_1209_, lean_object* v_a_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_zero_1218_; uint8_t v_isZero_1219_; 
v_zero_1218_ = lean_unsigned_to_nat(0u);
v_isZero_1219_ = lean_nat_dec_eq(v_i_1209_, v_zero_1218_);
if (v_isZero_1219_ == 1)
{
lean_object* v___x_1220_; 
lean_dec(v_i_1209_);
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v_a_1210_);
return v___x_1220_;
}
else
{
lean_object* v_one_1221_; lean_object* v_n_1222_; lean_object* v___y_1224_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_one_1221_ = lean_unsigned_to_nat(1u);
v_n_1222_ = lean_nat_sub(v_i_1209_, v_one_1221_);
lean_dec(v_i_1209_);
v___x_1227_ = lean_array_fget_borrowed(v_xs_1208_, v_n_1222_);
v___x_1228_ = l_Lean_Expr_fvarId_x21(v___x_1227_);
v___x_1229_ = l_Lean_FVarId_getDecl___redArg(v___x_1228_, v___y_1213_, v___y_1215_, v___y_1216_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v_a_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; lean_object* v___x_1236_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1230_);
lean_dec_ref(v___x_1229_);
v___x_1231_ = l_Lean_LocalDecl_type(v_a_1230_);
v___x_1232_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v___x_1231_, v_n_1222_, v_xs_1208_, v___y_1212_, v___y_1213_);
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref(v___x_1232_);
v___x_1234_ = l_Lean_LocalDecl_userName(v_a_1230_);
v___x_1235_ = l_Lean_LocalDecl_binderInfo(v_a_1230_);
lean_dec(v_a_1230_);
v___x_1236_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v___x_1234_, v___x_1235_, v_a_1233_, v_a_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
v___y_1224_ = v___x_1236_;
goto v___jp_1223_;
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec(v_n_1222_);
lean_dec_ref(v_a_1210_);
v_a_1237_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1229_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1229_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
v___jp_1223_:
{
if (lean_obj_tag(v___y_1224_) == 0)
{
lean_object* v_a_1225_; 
v_a_1225_ = lean_ctor_get(v___y_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref(v___y_1224_);
v_i_1209_ = v_n_1222_;
v_a_1210_ = v_a_1225_;
goto _start;
}
else
{
lean_dec(v_n_1222_);
return v___y_1224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg___boxed(lean_object* v_xs_1245_, lean_object* v_i_1246_, lean_object* v_a_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1245_, v_i_1246_, v_a_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec_ref(v_xs_1245_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS(lean_object* v_xs_1256_, lean_object* v_e_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_a_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1265_ = lean_unsigned_to_nat(0u);
v___x_1266_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v_e_1257_, v___x_1265_, v_xs_1256_, v_a_1259_, v_a_1260_);
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref(v___x_1266_);
v___x_1268_ = lean_array_get_size(v_xs_1256_);
v___x_1269_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1256_, v___x_1268_, v_a_1267_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS___boxed(lean_object* v_xs_1270_, lean_object* v_e_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_xs_1270_, v_e_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec_ref(v_xs_1270_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(lean_object* v_xs_1280_, lean_object* v_n_1281_, lean_object* v_i_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_1280_, v_i_1282_, v_a_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___boxed(lean_object* v_xs_1293_, lean_object* v_n_1294_, lean_object* v_i_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(v_xs_1293_, v_n_1294_, v_i_1295_, v_a_1296_, v_a_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v_n_1294_);
lean_dec_ref(v_xs_1293_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(lean_object* v_x_1306_, uint8_t v_bi_1307_, lean_object* v_t_1308_, lean_object* v_b_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___y_1318_; lean_object* v___x_1321_; uint8_t v_debug_1322_; 
v___x_1321_ = lean_st_ref_get(v___y_1311_);
v_debug_1322_ = lean_ctor_get_uint8(v___x_1321_, sizeof(void*)*10);
lean_dec(v___x_1321_);
if (v_debug_1322_ == 0)
{
v___y_1318_ = v___y_1311_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1323_; 
lean_inc_ref(v_t_1308_);
v___x_1323_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1308_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v___x_1324_; 
lean_dec_ref(v___x_1323_);
lean_inc_ref(v_b_1309_);
v___x_1324_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_dec_ref(v___x_1324_);
v___y_1318_ = v___y_1311_;
goto v___jp_1317_;
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec_ref(v_b_1309_);
lean_dec_ref(v_t_1308_);
lean_dec(v_x_1306_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec_ref(v_b_1309_);
lean_dec_ref(v_t_1308_);
lean_dec(v_x_1306_);
v_a_1333_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1323_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1323_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
v___jp_1317_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = l_Lean_Expr_forallE___override(v_x_1306_, v_t_1308_, v_b_1309_, v_bi_1307_);
v___x_1320_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1319_, v___y_1318_);
return v___x_1320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0___boxed(lean_object* v_x_1341_, lean_object* v_bi_1342_, lean_object* v_t_1343_, lean_object* v_b_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
uint8_t v_bi_boxed_1352_; lean_object* v_res_1353_; 
v_bi_boxed_1352_ = lean_unbox(v_bi_1342_);
v_res_1353_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v_x_1341_, v_bi_boxed_1352_, v_t_1343_, v_b_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(lean_object* v_xs_1354_, lean_object* v_i_1355_, lean_object* v_a_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_zero_1364_; uint8_t v_isZero_1365_; 
v_zero_1364_ = lean_unsigned_to_nat(0u);
v_isZero_1365_ = lean_nat_dec_eq(v_i_1355_, v_zero_1364_);
if (v_isZero_1365_ == 1)
{
lean_object* v___x_1366_; 
lean_dec(v_i_1355_);
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v_a_1356_);
return v___x_1366_;
}
else
{
lean_object* v_one_1367_; lean_object* v_n_1368_; lean_object* v___y_1370_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v_one_1367_ = lean_unsigned_to_nat(1u);
v_n_1368_ = lean_nat_sub(v_i_1355_, v_one_1367_);
lean_dec(v_i_1355_);
v___x_1373_ = lean_array_fget_borrowed(v_xs_1354_, v_n_1368_);
v___x_1374_ = l_Lean_Expr_fvarId_x21(v___x_1373_);
v___x_1375_ = l_Lean_FVarId_getDecl___redArg(v___x_1374_, v___y_1359_, v___y_1361_, v___y_1362_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v_a_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; lean_object* v___x_1382_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref(v___x_1375_);
v___x_1377_ = l_Lean_LocalDecl_type(v_a_1376_);
v___x_1378_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v___x_1377_, v_n_1368_, v_xs_1354_, v___y_1358_, v___y_1359_);
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref(v___x_1378_);
v___x_1380_ = l_Lean_LocalDecl_userName(v_a_1376_);
v___x_1381_ = l_Lean_LocalDecl_binderInfo(v_a_1376_);
lean_dec(v_a_1376_);
v___x_1382_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v___x_1380_, v___x_1381_, v_a_1379_, v_a_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
v___y_1370_ = v___x_1382_;
goto v___jp_1369_;
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_dec(v_n_1368_);
lean_dec_ref(v_a_1356_);
v_a_1383_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1375_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1375_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
v___jp_1369_:
{
if (lean_obj_tag(v___y_1370_) == 0)
{
lean_object* v_a_1371_; 
v_a_1371_ = lean_ctor_get(v___y_1370_, 0);
lean_inc(v_a_1371_);
lean_dec_ref(v___y_1370_);
v_i_1355_ = v_n_1368_;
v_a_1356_ = v_a_1371_;
goto _start;
}
else
{
lean_dec(v_n_1368_);
return v___y_1370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg___boxed(lean_object* v_xs_1391_, lean_object* v_i_1392_, lean_object* v_a_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1391_, v_i_1392_, v_a_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec_ref(v_xs_1391_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS(lean_object* v_xs_1402_, lean_object* v_e_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v_a_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1411_ = lean_unsigned_to_nat(0u);
v___x_1412_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(v_e_1403_, v___x_1411_, v_xs_1402_, v_a_1405_, v_a_1406_);
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref(v___x_1412_);
v___x_1414_ = lean_array_get_size(v_xs_1402_);
v___x_1415_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1402_, v___x_1414_, v_a_1413_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_mkForallFVarsS___boxed(lean_object* v_xs_1416_, lean_object* v_e_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_Meta_Sym_mkForallFVarsS(v_xs_1416_, v_e_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
lean_dec(v_a_1419_);
lean_dec_ref(v_a_1418_);
lean_dec_ref(v_xs_1416_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(lean_object* v_xs_1426_, lean_object* v_n_1427_, lean_object* v_i_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_1426_, v_i_1428_, v_a_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___boxed(lean_object* v_xs_1439_, lean_object* v_n_1440_, lean_object* v_i_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(v_xs_1439_, v_n_1440_, v_i_1441_, v_a_1442_, v_a_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v_n_1440_);
lean_dec_ref(v_xs_1439_);
return v_res_1451_;
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
