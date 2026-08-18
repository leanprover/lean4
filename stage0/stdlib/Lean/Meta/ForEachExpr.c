// Lean compiler output
// Module: Lean.Meta.ForEachExpr
// Imports: public import Lean.Meta.Basic import Init.Data.Range.Polymorphic.Iterators
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Lean_MonadCacheT_instMonad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadCacheT_instMonadControl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_withLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_MetavarContext_setMVarUserNameTemporarily(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_visitLambda___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_visitLambda___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_visitLambda___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_forEachExpr_x27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forEachExpr_x27___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_forEachExpr_x27___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forEachExpr_x27___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_forEachExpr_x27___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forEachExpr_x27___redArg___closed__2;
static lean_once_cell_t l_Lean_Meta_forEachExpr_x27___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_forEachExpr_x27___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__16___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__16___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_setMVarUserNamesAt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_setMVarUserNamesAt___closed__0 = (const lean_object*)&l_Lean_Meta_setMVarUserNamesAt___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_resetMVarUserNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_resetMVarUserNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_binderName_3_, uint8_t v_binderInfo_4_, lean_object* v_d_5_, lean_object* v___f_6_, lean_object* v_____r_7_){
_start:
{
uint8_t v___x_8_; lean_object* v___x_9_; 
v___x_8_ = 0;
v___x_9_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1_, v_inst_2_, v_binderName_3_, v_binderInfo_4_, v_d_5_, v___f_6_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1___boxed(lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_binderName_12_, lean_object* v_binderInfo_13_, lean_object* v_d_14_, lean_object* v___f_15_, lean_object* v_____r_16_){
_start:
{
uint8_t v_binderInfo_66__boxed_17_; lean_object* v_res_18_; 
v_binderInfo_66__boxed_17_ = lean_unbox(v_binderInfo_13_);
v_res_18_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1(v_inst_10_, v_inst_11_, v_binderName_12_, v_binderInfo_66__boxed_17_, v_d_14_, v___f_15_, v_____r_16_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg(lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_f_21_, lean_object* v_fvars_22_, lean_object* v_a_23_){
_start:
{
if (lean_obj_tag(v_a_23_) == 6)
{
lean_object* v_toBind_24_; lean_object* v_binderName_25_; lean_object* v_binderType_26_; lean_object* v_body_27_; uint8_t v_binderInfo_28_; lean_object* v___f_29_; lean_object* v_d_30_; lean_object* v___x_31_; lean_object* v___f_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_toBind_24_ = lean_ctor_get(v_inst_19_, 1);
lean_inc(v_toBind_24_);
v_binderName_25_ = lean_ctor_get(v_a_23_, 0);
lean_inc(v_binderName_25_);
v_binderType_26_ = lean_ctor_get(v_a_23_, 1);
lean_inc_ref(v_binderType_26_);
v_body_27_ = lean_ctor_get(v_a_23_, 2);
lean_inc_ref(v_body_27_);
v_binderInfo_28_ = lean_ctor_get_uint8(v_a_23_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_23_, 3);
lean_inc(v_f_21_);
lean_inc_ref(v_inst_20_);
lean_inc_ref(v_inst_19_);
lean_inc_ref(v_fvars_22_);
v___f_29_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__0), 6, 5);
lean_closure_set(v___f_29_, 0, v_fvars_22_);
lean_closure_set(v___f_29_, 1, v_inst_19_);
lean_closure_set(v___f_29_, 2, v_inst_20_);
lean_closure_set(v___f_29_, 3, v_f_21_);
lean_closure_set(v___f_29_, 4, v_body_27_);
v_d_30_ = lean_expr_instantiate_rev(v_binderType_26_, v_fvars_22_);
lean_dec_ref(v_fvars_22_);
lean_dec_ref(v_binderType_26_);
v___x_31_ = lean_box(v_binderInfo_28_);
lean_inc_ref(v_d_30_);
v___f_32_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_32_, 0, v_inst_20_);
lean_closure_set(v___f_32_, 1, v_inst_19_);
lean_closure_set(v___f_32_, 2, v_binderName_25_);
lean_closure_set(v___f_32_, 3, v___x_31_);
lean_closure_set(v___f_32_, 4, v_d_30_);
lean_closure_set(v___f_32_, 5, v___f_29_);
v___x_33_ = lean_apply_1(v_f_21_, v_d_30_);
v___x_34_ = lean_apply_4(v_toBind_24_, lean_box(0), lean_box(0), v___x_33_, v___f_32_);
return v___x_34_;
}
else
{
lean_object* v___x_35_; lean_object* v___x_36_; 
lean_dec_ref(v_inst_20_);
lean_dec_ref(v_inst_19_);
v___x_35_ = lean_expr_instantiate_rev(v_a_23_, v_fvars_22_);
lean_dec_ref(v_fvars_22_);
lean_dec_ref(v_a_23_);
v___x_36_ = lean_apply_1(v_f_21_, v___x_35_);
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__0(lean_object* v_fvars_37_, lean_object* v_inst_38_, lean_object* v_inst_39_, lean_object* v_f_40_, lean_object* v_body_41_, lean_object* v_x_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_array_push(v_fvars_37_, v_x_42_);
v___x_44_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg(v_inst_38_, v_inst_39_, v_f_40_, v___x_43_, v_body_41_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit(lean_object* v_m_45_, lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_f_48_, lean_object* v_fvars_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg(v_inst_46_, v_inst_47_, v_f_48_, v_fvars_49_, v_a_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___redArg(lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_f_56_, lean_object* v_e_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_59_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg(v_inst_54_, v_inst_55_, v_f_56_, v___x_58_, v_e_57_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda(lean_object* v_m_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_f_63_, lean_object* v_e_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Meta_visitLambda___redArg(v_inst_61_, v_inst_62_, v_f_63_, v_e_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg(lean_object* v_inst_66_, lean_object* v_inst_67_, lean_object* v_f_68_, lean_object* v_fvars_69_, lean_object* v_a_70_){
_start:
{
if (lean_obj_tag(v_a_70_) == 7)
{
lean_object* v_toBind_71_; lean_object* v_binderName_72_; lean_object* v_binderType_73_; lean_object* v_body_74_; uint8_t v_binderInfo_75_; lean_object* v___f_76_; lean_object* v_d_77_; lean_object* v___x_78_; lean_object* v___f_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_toBind_71_ = lean_ctor_get(v_inst_66_, 1);
lean_inc(v_toBind_71_);
v_binderName_72_ = lean_ctor_get(v_a_70_, 0);
lean_inc(v_binderName_72_);
v_binderType_73_ = lean_ctor_get(v_a_70_, 1);
lean_inc_ref(v_binderType_73_);
v_body_74_ = lean_ctor_get(v_a_70_, 2);
lean_inc_ref(v_body_74_);
v_binderInfo_75_ = lean_ctor_get_uint8(v_a_70_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_70_, 3);
lean_inc(v_f_68_);
lean_inc_ref(v_inst_67_);
lean_inc_ref(v_inst_66_);
lean_inc_ref(v_fvars_69_);
v___f_76_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg___lam__0), 6, 5);
lean_closure_set(v___f_76_, 0, v_fvars_69_);
lean_closure_set(v___f_76_, 1, v_inst_66_);
lean_closure_set(v___f_76_, 2, v_inst_67_);
lean_closure_set(v___f_76_, 3, v_f_68_);
lean_closure_set(v___f_76_, 4, v_body_74_);
v_d_77_ = lean_expr_instantiate_rev(v_binderType_73_, v_fvars_69_);
lean_dec_ref(v_fvars_69_);
lean_dec_ref(v_binderType_73_);
v___x_78_ = lean_box(v_binderInfo_75_);
lean_inc_ref(v_d_77_);
v___f_79_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_79_, 0, v_inst_67_);
lean_closure_set(v___f_79_, 1, v_inst_66_);
lean_closure_set(v___f_79_, 2, v_binderName_72_);
lean_closure_set(v___f_79_, 3, v___x_78_);
lean_closure_set(v___f_79_, 4, v_d_77_);
lean_closure_set(v___f_79_, 5, v___f_76_);
v___x_80_ = lean_apply_1(v_f_68_, v_d_77_);
v___x_81_ = lean_apply_4(v_toBind_71_, lean_box(0), lean_box(0), v___x_80_, v___f_79_);
return v___x_81_;
}
else
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec_ref(v_inst_67_);
lean_dec_ref(v_inst_66_);
v___x_82_ = lean_expr_instantiate_rev(v_a_70_, v_fvars_69_);
lean_dec_ref(v_fvars_69_);
lean_dec_ref(v_a_70_);
v___x_83_ = lean_apply_1(v_f_68_, v___x_82_);
return v___x_83_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg___lam__0(lean_object* v_fvars_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_f_87_, lean_object* v_body_88_, lean_object* v_x_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_array_push(v_fvars_84_, v_x_89_);
v___x_91_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg(v_inst_85_, v_inst_86_, v_f_87_, v___x_90_, v_body_88_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit(lean_object* v_m_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_f_95_, lean_object* v_fvars_96_, lean_object* v_a_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg(v_inst_93_, v_inst_94_, v_f_95_, v_fvars_96_, v_a_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___redArg(lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_f_101_, lean_object* v_e_102_){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_104_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg(v_inst_99_, v_inst_100_, v_f_101_, v___x_103_, v_e_102_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall(lean_object* v_m_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_f_108_, lean_object* v_e_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Meta_visitForall___redArg(v_inst_106_, v_inst_107_, v_f_108_, v_e_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__1(lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_declName_113_, lean_object* v_d_114_, lean_object* v_v_115_, lean_object* v___f_116_, lean_object* v_____r_117_){
_start:
{
uint8_t v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; 
v___x_118_ = 0;
v___x_119_ = 0;
v___x_120_ = l_Lean_Meta_withLetDecl___redArg(v_inst_111_, v_inst_112_, v_declName_113_, v_d_114_, v_v_115_, v___f_116_, v___x_118_, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__2(lean_object* v_f_121_, lean_object* v_v_122_, lean_object* v_toBind_123_, lean_object* v___f_124_, lean_object* v_____r_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_apply_1(v_f_121_, v_v_122_);
v___x_127_ = lean_apply_4(v_toBind_123_, lean_box(0), lean_box(0), v___x_126_, v___f_124_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg(lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_f_130_, lean_object* v_fvars_131_, lean_object* v_a_132_){
_start:
{
if (lean_obj_tag(v_a_132_) == 8)
{
lean_object* v_toBind_133_; lean_object* v_declName_134_; lean_object* v_type_135_; lean_object* v_value_136_; lean_object* v_body_137_; lean_object* v___f_138_; lean_object* v_d_139_; lean_object* v_v_140_; lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_toBind_133_ = lean_ctor_get(v_inst_128_, 1);
lean_inc_n(v_toBind_133_, 2);
v_declName_134_ = lean_ctor_get(v_a_132_, 0);
lean_inc(v_declName_134_);
v_type_135_ = lean_ctor_get(v_a_132_, 1);
lean_inc_ref(v_type_135_);
v_value_136_ = lean_ctor_get(v_a_132_, 2);
lean_inc_ref(v_value_136_);
v_body_137_ = lean_ctor_get(v_a_132_, 3);
lean_inc_ref(v_body_137_);
lean_dec_ref_known(v_a_132_, 4);
lean_inc_n(v_f_130_, 2);
lean_inc_ref(v_inst_129_);
lean_inc_ref(v_inst_128_);
lean_inc_ref(v_fvars_131_);
v___f_138_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__0), 6, 5);
lean_closure_set(v___f_138_, 0, v_fvars_131_);
lean_closure_set(v___f_138_, 1, v_inst_128_);
lean_closure_set(v___f_138_, 2, v_inst_129_);
lean_closure_set(v___f_138_, 3, v_f_130_);
lean_closure_set(v___f_138_, 4, v_body_137_);
v_d_139_ = lean_expr_instantiate_rev(v_type_135_, v_fvars_131_);
lean_dec_ref(v_type_135_);
v_v_140_ = lean_expr_instantiate_rev(v_value_136_, v_fvars_131_);
lean_dec_ref(v_fvars_131_);
lean_dec_ref(v_value_136_);
lean_inc_ref(v_v_140_);
lean_inc_ref(v_d_139_);
v___f_141_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__1), 7, 6);
lean_closure_set(v___f_141_, 0, v_inst_129_);
lean_closure_set(v___f_141_, 1, v_inst_128_);
lean_closure_set(v___f_141_, 2, v_declName_134_);
lean_closure_set(v___f_141_, 3, v_d_139_);
lean_closure_set(v___f_141_, 4, v_v_140_);
lean_closure_set(v___f_141_, 5, v___f_138_);
v___f_142_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__2), 5, 4);
lean_closure_set(v___f_142_, 0, v_f_130_);
lean_closure_set(v___f_142_, 1, v_v_140_);
lean_closure_set(v___f_142_, 2, v_toBind_133_);
lean_closure_set(v___f_142_, 3, v___f_141_);
v___x_143_ = lean_apply_1(v_f_130_, v_d_139_);
v___x_144_ = lean_apply_4(v_toBind_133_, lean_box(0), lean_box(0), v___x_143_, v___f_142_);
return v___x_144_;
}
else
{
lean_object* v___x_145_; lean_object* v___x_146_; 
lean_dec_ref(v_inst_129_);
lean_dec_ref(v_inst_128_);
v___x_145_ = lean_expr_instantiate_rev(v_a_132_, v_fvars_131_);
lean_dec_ref(v_fvars_131_);
lean_dec_ref(v_a_132_);
v___x_146_ = lean_apply_1(v_f_130_, v___x_145_);
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__0(lean_object* v_fvars_147_, lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_f_150_, lean_object* v_body_151_, lean_object* v_x_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_array_push(v_fvars_147_, v_x_152_);
v___x_154_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg(v_inst_148_, v_inst_149_, v_f_150_, v___x_153_, v_body_151_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit(lean_object* v_m_155_, lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_f_158_, lean_object* v_fvars_159_, lean_object* v_a_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg(v_inst_156_, v_inst_157_, v_f_158_, v_fvars_159_, v_a_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___redArg(lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_f_164_, lean_object* v_e_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_167_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg(v_inst_162_, v_inst_163_, v_f_164_, v___x_166_, v_e_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet(lean_object* v_m_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_f_171_, lean_object* v_e_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Meta_visitLet___redArg(v_inst_169_, v_inst_170_, v_f_171_, v_e_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__0(lean_object* v_toApplicative_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_toPure_177_; lean_object* v___x_178_; 
v_toPure_177_ = lean_ctor_get(v_toApplicative_174_, 1);
lean_inc(v_toPure_177_);
lean_dec_ref(v_toApplicative_174_);
v___x_178_ = lean_apply_2(v_toPure_177_, lean_box(0), v_a_175_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__1(lean_object* v___x_179_, lean_object* v___x_180_, lean_object* v_e_181_, lean_object* v_a_182_, lean_object* v_s_183_){
_start:
{
lean_object* v___x_184_; lean_object* v___y_186_; lean_object* v_i_187_; lean_object* v___y_194_; lean_object* v___y_206_; lean_object* v_i_207_; lean_object* v___x_225_; 
v___x_184_ = lean_box(0);
lean_inc_ref(v_e_181_);
lean_inc_ref(v___x_180_);
lean_inc_ref(v___x_179_);
v___x_225_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_179_, v___x_180_, v_s_183_, v_e_181_);
switch(lean_obj_tag(v___x_225_))
{
case 0:
{
lean_object* v_index_226_; lean_object* v_size_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec_ref(v___x_180_);
lean_dec_ref(v___x_179_);
v_index_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_index_226_);
lean_dec_ref_known(v___x_225_, 3);
v_size_227_ = lean_ctor_get(v_s_183_, 0);
lean_inc(v_size_227_);
v___x_228_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_183_, v_size_227_, v_index_226_, v_e_181_, v_a_182_);
lean_dec(v_index_226_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_184_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
return v___x_229_;
}
case 1:
{
lean_object* v_index_230_; lean_object* v_size_231_; lean_object* v_keyArray_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v_index_230_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_index_230_);
lean_dec_ref_known(v___x_225_, 1);
v_size_231_ = lean_ctor_get(v_s_183_, 0);
v_keyArray_232_ = lean_ctor_get(v_s_183_, 1);
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_nat_add(v_size_231_, v___x_233_);
v___x_235_ = lean_array_get_size(v_keyArray_232_);
v___x_236_ = lean_nat_dec_lt(v___x_234_, v___x_235_);
if (v___x_236_ == 0)
{
lean_dec(v___x_234_);
lean_dec(v_index_230_);
goto v___jp_213_;
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v___x_237_ = lean_unsigned_to_nat(4u);
v___x_238_ = lean_nat_mul(v___x_234_, v___x_237_);
v___x_239_ = lean_unsigned_to_nat(3u);
v___x_240_ = lean_nat_mul(v___x_235_, v___x_239_);
v___x_241_ = lean_nat_dec_le(v___x_238_, v___x_240_);
lean_dec(v___x_240_);
lean_dec(v___x_238_);
if (v___x_241_ == 0)
{
lean_dec(v___x_234_);
lean_dec(v_index_230_);
goto v___jp_213_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec_ref(v___x_180_);
lean_dec_ref(v___x_179_);
v___x_242_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_183_, v___x_234_, v_index_230_, v_e_181_, v_a_182_);
lean_dec(v_index_230_);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_184_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
return v___x_243_;
}
}
}
default: 
{
lean_object* v_size_244_; lean_object* v_keyArray_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v_size_244_ = lean_ctor_get(v_s_183_, 0);
v_keyArray_245_ = lean_ctor_get(v_s_183_, 1);
v___x_246_ = lean_unsigned_to_nat(1u);
v___x_247_ = lean_nat_add(v_size_244_, v___x_246_);
v___x_248_ = lean_array_get_size(v_keyArray_245_);
v___x_249_ = lean_nat_dec_lt(v___x_247_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_dec(v___x_247_);
lean_inc_ref(v___x_180_);
lean_inc_ref(v___x_179_);
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_179_, v___x_180_, v_s_183_);
v___y_194_ = v___x_250_;
goto v___jp_193_;
}
else
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_251_ = lean_unsigned_to_nat(4u);
v___x_252_ = lean_nat_mul(v___x_247_, v___x_251_);
lean_dec(v___x_247_);
v___x_253_ = lean_unsigned_to_nat(3u);
v___x_254_ = lean_nat_mul(v___x_248_, v___x_253_);
v___x_255_ = lean_nat_dec_le(v___x_252_, v___x_254_);
lean_dec(v___x_254_);
lean_dec(v___x_252_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
lean_inc_ref(v___x_180_);
lean_inc_ref(v___x_179_);
v___x_256_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_179_, v___x_180_, v_s_183_);
v___y_194_ = v___x_256_;
goto v___jp_193_;
}
else
{
v___y_194_ = v_s_183_;
goto v___jp_193_;
}
}
}
}
v___jp_185_:
{
lean_object* v_size_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_size_188_ = lean_ctor_get(v___y_186_, 0);
v___x_189_ = lean_unsigned_to_nat(1u);
v___x_190_ = lean_nat_add(v_size_188_, v___x_189_);
v___x_191_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_186_, v___x_190_, v_i_187_, v_e_181_, v_a_182_);
lean_dec(v_i_187_);
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_184_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
return v___x_192_;
}
v___jp_193_:
{
lean_object* v___x_195_; 
lean_inc_ref(v_e_181_);
v___x_195_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_179_, v___x_180_, v___y_194_, v_e_181_);
switch(lean_obj_tag(v___x_195_))
{
case 0:
{
lean_object* v_index_196_; lean_object* v_size_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_index_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_index_196_);
lean_dec_ref_known(v___x_195_, 3);
v_size_197_ = lean_ctor_get(v___y_194_, 0);
lean_inc(v_size_197_);
v___x_198_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_194_, v_size_197_, v_index_196_, v_e_181_, v_a_182_);
lean_dec(v_index_196_);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_184_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
return v___x_199_;
}
case 1:
{
lean_object* v_index_200_; 
v_index_200_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_index_200_);
lean_dec_ref_known(v___x_195_, 1);
v___y_186_ = v___y_194_;
v_i_187_ = v_index_200_;
goto v___jp_185_;
}
default: 
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_194_, v___x_201_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_index_203_; 
v_index_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_index_203_);
lean_dec_ref_known(v___x_202_, 1);
v___y_186_ = v___y_194_;
v_i_187_ = v_index_203_;
goto v___jp_185_;
}
else
{
lean_object* v___x_204_; 
lean_dec_ref(v_e_181_);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_184_);
lean_ctor_set(v___x_204_, 1, v___y_194_);
return v___x_204_;
}
}
}
}
v___jp_205_:
{
lean_object* v_size_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_size_208_ = lean_ctor_get(v___y_206_, 0);
v___x_209_ = lean_unsigned_to_nat(1u);
v___x_210_ = lean_nat_add(v_size_208_, v___x_209_);
v___x_211_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_206_, v___x_210_, v_i_207_, v_e_181_, v_a_182_);
lean_dec(v_i_207_);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_184_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
return v___x_212_;
}
v___jp_213_:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_inc_ref(v___x_180_);
lean_inc_ref(v___x_179_);
v___x_214_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___x_179_, v___x_180_, v_s_183_);
lean_inc_ref(v_e_181_);
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___x_179_, v___x_180_, v___x_214_, v_e_181_);
switch(lean_obj_tag(v___x_215_))
{
case 0:
{
lean_object* v_index_216_; lean_object* v_size_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_index_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_index_216_);
lean_dec_ref_known(v___x_215_, 3);
v_size_217_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_size_217_);
v___x_218_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_214_, v_size_217_, v_index_216_, v_e_181_, v_a_182_);
lean_dec(v_index_216_);
v___x_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_184_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
return v___x_219_;
}
case 1:
{
lean_object* v_index_220_; 
v_index_220_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_index_220_);
lean_dec_ref_known(v___x_215_, 1);
v___y_206_ = v___x_214_;
v_i_207_ = v_index_220_;
goto v___jp_205_;
}
default: 
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_214_, v___x_221_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_index_223_; 
v_index_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_index_223_);
lean_dec_ref_known(v___x_222_, 1);
v___y_206_ = v___x_214_;
v_i_207_ = v_index_223_;
goto v___jp_205_;
}
else
{
lean_object* v___x_224_; 
lean_dec_ref(v_e_181_);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_184_);
lean_ctor_set(v___x_224_, 1, v___x_214_);
return v___x_224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__2(lean_object* v_toApplicative_257_, lean_object* v___x_258_, lean_object* v___x_259_, lean_object* v_e_260_, lean_object* v_a_261_, lean_object* v_x_262_, lean_object* v_toBind_263_, lean_object* v_a_264_){
_start:
{
lean_object* v___f_265_; lean_object* v___f_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___f_265_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__0), 3, 2);
lean_closure_set(v___f_265_, 0, v_toApplicative_257_);
lean_closure_set(v___f_265_, 1, v_a_264_);
v___f_266_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__1), 5, 4);
lean_closure_set(v___f_266_, 0, v___x_258_);
lean_closure_set(v___f_266_, 1, v___x_259_);
lean_closure_set(v___f_266_, 2, v_e_260_);
lean_closure_set(v___f_266_, 3, v_a_264_);
lean_inc(v_a_261_);
v___x_267_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_267_, 0, lean_box(0));
lean_closure_set(v___x_267_, 1, lean_box(0));
lean_closure_set(v___x_267_, 2, lean_box(0));
lean_closure_set(v___x_267_, 3, v_a_261_);
lean_closure_set(v___x_267_, 4, v___f_266_);
v___x_268_ = lean_apply_2(v_x_262_, lean_box(0), v___x_267_);
v___x_269_ = lean_apply_4(v_toBind_263_, lean_box(0), lean_box(0), v___x_268_, v___f_265_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_270_, lean_object* v___x_271_, lean_object* v___x_272_, lean_object* v_e_273_, lean_object* v_a_274_, lean_object* v_x_275_, lean_object* v_toBind_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__2(v_toApplicative_270_, v___x_271_, v___x_272_, v_e_273_, v_a_274_, v_x_275_, v_toBind_276_, v_a_277_);
lean_dec(v_a_274_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__3(lean_object* v_toApplicative_279_, lean_object* v___x_280_, lean_object* v___x_281_, lean_object* v_e_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_toPure_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_toPure_284_ = lean_ctor_get(v_toApplicative_279_, 1);
lean_inc(v_toPure_284_);
lean_dec_ref(v_toApplicative_279_);
v___x_285_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_280_, v___x_281_, v_a_283_, v_e_282_);
v___x_286_ = lean_apply_2(v_toPure_284_, lean_box(0), v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__3___boxed(lean_object* v_toApplicative_287_, lean_object* v___x_288_, lean_object* v___x_289_, lean_object* v_e_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__3(v_toApplicative_287_, v___x_288_, v___x_289_, v_e_290_, v_a_291_);
lean_dec_ref(v_a_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__6(lean_object* v_fn_293_, lean_object* v_e_294_, lean_object* v_toBind_295_, lean_object* v___f_296_, lean_object* v___f_297_, lean_object* v_toApplicative_298_, lean_object* v_a_299_){
_start:
{
if (lean_obj_tag(v_a_299_) == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec_ref(v_toApplicative_298_);
v___x_300_ = lean_apply_1(v_fn_293_, v_e_294_);
lean_inc(v_toBind_295_);
v___x_301_ = lean_apply_4(v_toBind_295_, lean_box(0), lean_box(0), v___x_300_, v___f_296_);
v___x_302_ = lean_apply_4(v_toBind_295_, lean_box(0), lean_box(0), v___x_301_, v___f_297_);
return v___x_302_;
}
else
{
lean_object* v_val_303_; lean_object* v_toPure_304_; lean_object* v___x_305_; 
lean_dec(v___f_297_);
lean_dec(v___f_296_);
lean_dec(v_toBind_295_);
lean_dec_ref(v_e_294_);
lean_dec(v_fn_293_);
v_val_303_ = lean_ctor_get(v_a_299_, 0);
lean_inc(v_val_303_);
lean_dec_ref_known(v_a_299_, 1);
v_toPure_304_ = lean_ctor_get(v_toApplicative_298_, 1);
lean_inc(v_toPure_304_);
lean_dec_ref(v_toApplicative_298_);
v___x_305_ = lean_apply_2(v_toPure_304_, lean_box(0), v_val_303_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed(lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_fn_310_, lean_object* v_x_311_, lean_object* v_x_312_, lean_object* v_e_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_308_, v_inst_309_, v_fn_310_, v_x_311_, v_x_312_, v_e_313_, v_a_314_);
lean_dec(v_a_314_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4___boxed(lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_fn_318_, lean_object* v_x_319_, lean_object* v_x_320_, lean_object* v_arg_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4(v_inst_316_, v_inst_317_, v_fn_318_, v_x_319_, v_x_320_, v_arg_321_, v_a_322_, v_a_323_);
lean_dec(v_a_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5(lean_object* v_toApplicative_325_, lean_object* v_e_326_, lean_object* v_x_327_, lean_object* v___x_328_, lean_object* v___x_329_, lean_object* v_inst_330_, lean_object* v_inst_331_, lean_object* v_fn_332_, lean_object* v_x_333_, lean_object* v___x_334_, lean_object* v_a_335_, lean_object* v_toBind_336_, uint8_t v_a_337_){
_start:
{
if (v_a_337_ == 0)
{
lean_object* v_toPure_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec(v_toBind_336_);
lean_dec_ref(v___x_334_);
lean_dec(v_x_333_);
lean_dec(v_fn_332_);
lean_dec_ref(v_inst_331_);
lean_dec_ref(v_inst_330_);
lean_dec_ref(v___x_329_);
lean_dec_ref(v___x_328_);
lean_dec_ref(v_e_326_);
v_toPure_338_ = lean_ctor_get(v_toApplicative_325_, 1);
lean_inc(v_toPure_338_);
lean_dec_ref(v_toApplicative_325_);
v___x_339_ = lean_box(0);
v___x_340_ = lean_apply_2(v_toPure_338_, lean_box(0), v___x_339_);
return v___x_340_;
}
else
{
switch(lean_obj_tag(v_e_326_))
{
case 7:
{
lean_object* v___x_341_; lean_object* v___f_342_; lean_object* v___f_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_1537__overap_346_; lean_object* v___x_347_; 
lean_dec(v_toBind_336_);
lean_dec_ref(v_toApplicative_325_);
v___x_341_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_327_, v___x_328_, v___x_329_);
lean_inc_ref_n(v_inst_330_, 2);
lean_inc_ref(v___x_341_);
v___f_342_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_342_, 0, v___x_341_);
lean_closure_set(v___f_342_, 1, v_inst_330_);
v___f_343_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_343_, 0, v___x_341_);
lean_closure_set(v___f_343_, 1, v_inst_330_);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v___f_342_);
lean_ctor_set(v___x_344_, 1, v___f_343_);
v___x_345_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed), 7, 5);
lean_closure_set(v___x_345_, 0, v_inst_331_);
lean_closure_set(v___x_345_, 1, v_inst_330_);
lean_closure_set(v___x_345_, 2, v_fn_332_);
lean_closure_set(v___x_345_, 3, v_x_327_);
lean_closure_set(v___x_345_, 4, v_x_333_);
v___x_1537__overap_346_ = l_Lean_Meta_visitForall___redArg(v___x_334_, v___x_344_, v___x_345_, v_e_326_);
lean_inc(v_a_335_);
v___x_347_ = lean_apply_1(v___x_1537__overap_346_, v_a_335_);
return v___x_347_;
}
case 6:
{
lean_object* v___x_348_; lean_object* v___f_349_; lean_object* v___f_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_1547__overap_353_; lean_object* v___x_354_; 
lean_dec(v_toBind_336_);
lean_dec_ref(v_toApplicative_325_);
v___x_348_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_327_, v___x_328_, v___x_329_);
lean_inc_ref_n(v_inst_330_, 2);
lean_inc_ref(v___x_348_);
v___f_349_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_349_, 0, v___x_348_);
lean_closure_set(v___f_349_, 1, v_inst_330_);
v___f_350_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_350_, 0, v___x_348_);
lean_closure_set(v___f_350_, 1, v_inst_330_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v___f_349_);
lean_ctor_set(v___x_351_, 1, v___f_350_);
v___x_352_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed), 7, 5);
lean_closure_set(v___x_352_, 0, v_inst_331_);
lean_closure_set(v___x_352_, 1, v_inst_330_);
lean_closure_set(v___x_352_, 2, v_fn_332_);
lean_closure_set(v___x_352_, 3, v_x_327_);
lean_closure_set(v___x_352_, 4, v_x_333_);
v___x_1547__overap_353_ = l_Lean_Meta_visitLambda___redArg(v___x_334_, v___x_351_, v___x_352_, v_e_326_);
lean_inc(v_a_335_);
v___x_354_ = lean_apply_1(v___x_1547__overap_353_, v_a_335_);
return v___x_354_;
}
case 8:
{
lean_object* v___x_355_; lean_object* v___f_356_; lean_object* v___f_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_1558__overap_360_; lean_object* v___x_361_; 
lean_dec(v_toBind_336_);
lean_dec_ref(v_toApplicative_325_);
v___x_355_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_327_, v___x_328_, v___x_329_);
lean_inc_ref_n(v_inst_330_, 2);
lean_inc_ref(v___x_355_);
v___f_356_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_356_, 0, v___x_355_);
lean_closure_set(v___f_356_, 1, v_inst_330_);
v___f_357_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_357_, 0, v___x_355_);
lean_closure_set(v___f_357_, 1, v_inst_330_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___f_356_);
lean_ctor_set(v___x_358_, 1, v___f_357_);
v___x_359_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed), 7, 5);
lean_closure_set(v___x_359_, 0, v_inst_331_);
lean_closure_set(v___x_359_, 1, v_inst_330_);
lean_closure_set(v___x_359_, 2, v_fn_332_);
lean_closure_set(v___x_359_, 3, v_x_327_);
lean_closure_set(v___x_359_, 4, v_x_333_);
v___x_1558__overap_360_ = l_Lean_Meta_visitLet___redArg(v___x_334_, v___x_358_, v___x_359_, v_e_326_);
lean_inc(v_a_335_);
v___x_361_ = lean_apply_1(v___x_1558__overap_360_, v_a_335_);
return v___x_361_;
}
case 5:
{
lean_object* v_fn_362_; lean_object* v_arg_363_; lean_object* v___f_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
lean_dec_ref(v___x_334_);
lean_dec_ref(v___x_329_);
lean_dec_ref(v___x_328_);
lean_dec_ref(v_toApplicative_325_);
v_fn_362_ = lean_ctor_get(v_e_326_, 0);
lean_inc_ref(v_fn_362_);
v_arg_363_ = lean_ctor_get(v_e_326_, 1);
lean_inc_ref(v_arg_363_);
lean_dec_ref_known(v_e_326_, 2);
lean_inc(v_a_335_);
lean_inc(v_x_333_);
lean_inc(v_fn_332_);
lean_inc_ref(v_inst_330_);
lean_inc_ref(v_inst_331_);
v___f_364_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_364_, 0, v_inst_331_);
lean_closure_set(v___f_364_, 1, v_inst_330_);
lean_closure_set(v___f_364_, 2, v_fn_332_);
lean_closure_set(v___f_364_, 3, v_x_327_);
lean_closure_set(v___f_364_, 4, v_x_333_);
lean_closure_set(v___f_364_, 5, v_arg_363_);
lean_closure_set(v___f_364_, 6, v_a_335_);
v___x_365_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_331_, v_inst_330_, v_fn_332_, v_x_327_, v_x_333_, v_fn_362_, v_a_335_);
v___x_366_ = lean_apply_4(v_toBind_336_, lean_box(0), lean_box(0), v___x_365_, v___f_364_);
return v___x_366_;
}
case 10:
{
lean_object* v_expr_367_; lean_object* v___x_368_; 
lean_dec(v_toBind_336_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v___x_329_);
lean_dec_ref(v___x_328_);
lean_dec_ref(v_toApplicative_325_);
v_expr_367_ = lean_ctor_get(v_e_326_, 1);
lean_inc_ref(v_expr_367_);
lean_dec_ref_known(v_e_326_, 2);
v___x_368_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_331_, v_inst_330_, v_fn_332_, v_x_327_, v_x_333_, v_expr_367_, v_a_335_);
return v___x_368_;
}
case 11:
{
lean_object* v_struct_369_; lean_object* v___x_370_; 
lean_dec(v_toBind_336_);
lean_dec_ref(v___x_334_);
lean_dec_ref(v___x_329_);
lean_dec_ref(v___x_328_);
lean_dec_ref(v_toApplicative_325_);
v_struct_369_ = lean_ctor_get(v_e_326_, 2);
lean_inc_ref(v_struct_369_);
lean_dec_ref_known(v_e_326_, 3);
v___x_370_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_331_, v_inst_330_, v_fn_332_, v_x_327_, v_x_333_, v_struct_369_, v_a_335_);
return v___x_370_;
}
default: 
{
lean_object* v_toPure_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
lean_dec(v_toBind_336_);
lean_dec_ref(v___x_334_);
lean_dec(v_x_333_);
lean_dec(v_fn_332_);
lean_dec_ref(v_inst_331_);
lean_dec_ref(v_inst_330_);
lean_dec_ref(v___x_329_);
lean_dec_ref(v___x_328_);
lean_dec_ref(v_e_326_);
v_toPure_371_ = lean_ctor_get(v_toApplicative_325_, 1);
lean_inc(v_toPure_371_);
lean_dec_ref(v_toApplicative_325_);
v___x_372_ = lean_box(0);
v___x_373_ = lean_apply_2(v_toPure_371_, lean_box(0), v___x_372_);
return v___x_373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___boxed(lean_object* v_toApplicative_374_, lean_object* v_e_375_, lean_object* v_x_376_, lean_object* v___x_377_, lean_object* v___x_378_, lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_fn_381_, lean_object* v_x_382_, lean_object* v___x_383_, lean_object* v_a_384_, lean_object* v_toBind_385_, lean_object* v_a_386_){
_start:
{
uint8_t v_a_boxed_387_; lean_object* v_res_388_; 
v_a_boxed_387_ = lean_unbox(v_a_386_);
v_res_388_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5(v_toApplicative_374_, v_e_375_, v_x_376_, v___x_377_, v___x_378_, v_inst_379_, v_inst_380_, v_fn_381_, v_x_382_, v___x_383_, v_a_384_, v_toBind_385_, v_a_boxed_387_);
lean_dec(v_a_384_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_fn_391_, lean_object* v_x_392_, lean_object* v_x_393_, lean_object* v_e_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v_toApplicative_399_; lean_object* v_toBind_400_; lean_object* v___f_401_; lean_object* v___f_402_; lean_object* v___f_403_; lean_object* v___f_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_396_ = ((lean_object*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__0));
v___x_397_ = ((lean_object*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__1));
lean_inc_ref(v_inst_389_);
v___x_398_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_392_, v___x_396_, v___x_397_, v_inst_389_);
v_toApplicative_399_ = lean_ctor_get(v_inst_389_, 0);
lean_inc_ref_n(v_toApplicative_399_, 4);
v_toBind_400_ = lean_ctor_get(v_inst_389_, 1);
lean_inc_n(v_toBind_400_, 5);
lean_inc_n(v_x_393_, 2);
lean_inc_n(v_a_395_, 3);
lean_inc_ref_n(v_e_394_, 3);
v___f_401_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_401_, 0, v_toApplicative_399_);
lean_closure_set(v___f_401_, 1, v___x_396_);
lean_closure_set(v___f_401_, 2, v___x_397_);
lean_closure_set(v___f_401_, 3, v_e_394_);
lean_closure_set(v___f_401_, 4, v_a_395_);
lean_closure_set(v___f_401_, 5, v_x_393_);
lean_closure_set(v___f_401_, 6, v_toBind_400_);
v___f_402_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_402_, 0, v_toApplicative_399_);
lean_closure_set(v___f_402_, 1, v___x_396_);
lean_closure_set(v___f_402_, 2, v___x_397_);
lean_closure_set(v___f_402_, 3, v_e_394_);
lean_inc(v_fn_391_);
v___f_403_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_403_, 0, v_toApplicative_399_);
lean_closure_set(v___f_403_, 1, v_e_394_);
lean_closure_set(v___f_403_, 2, v_x_392_);
lean_closure_set(v___f_403_, 3, v___x_396_);
lean_closure_set(v___f_403_, 4, v___x_397_);
lean_closure_set(v___f_403_, 5, v_inst_390_);
lean_closure_set(v___f_403_, 6, v_inst_389_);
lean_closure_set(v___f_403_, 7, v_fn_391_);
lean_closure_set(v___f_403_, 8, v_x_393_);
lean_closure_set(v___f_403_, 9, v___x_398_);
lean_closure_set(v___f_403_, 10, v_a_395_);
lean_closure_set(v___f_403_, 11, v_toBind_400_);
v___f_404_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__6), 7, 6);
lean_closure_set(v___f_404_, 0, v_fn_391_);
lean_closure_set(v___f_404_, 1, v_e_394_);
lean_closure_set(v___f_404_, 2, v_toBind_400_);
lean_closure_set(v___f_404_, 3, v___f_403_);
lean_closure_set(v___f_404_, 4, v___f_401_);
lean_closure_set(v___f_404_, 5, v_toApplicative_399_);
v___x_405_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_405_, 0, lean_box(0));
lean_closure_set(v___x_405_, 1, lean_box(0));
lean_closure_set(v___x_405_, 2, v_a_395_);
v___x_406_ = lean_apply_2(v_x_393_, lean_box(0), v___x_405_);
v___x_407_ = lean_apply_4(v_toBind_400_, lean_box(0), lean_box(0), v___x_406_, v___f_402_);
v___x_408_ = lean_apply_4(v_toBind_400_, lean_box(0), lean_box(0), v___x_407_, v___f_404_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4(lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_fn_411_, lean_object* v_x_412_, lean_object* v_x_413_, lean_object* v_arg_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_409_, v_inst_410_, v_fn_411_, v_x_412_, v_x_413_, v_arg_414_, v_a_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit(lean_object* v_m_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_fn_421_, lean_object* v_x_422_, lean_object* v_x_423_, lean_object* v_e_424_, lean_object* v_a_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_419_, v_inst_420_, v_fn_421_, v_x_422_, v_x_423_, v_e_424_, v_a_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___boxed(lean_object* v_m_427_, lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_fn_430_, lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_e_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit(v_m_427_, v_inst_428_, v_inst_429_, v_fn_430_, v_x_431_, v_x_432_, v_e_433_, v_a_434_);
lean_dec(v_a_434_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__0(lean_object* v_x_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_apply_1(v_x_436_, lean_box(0));
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__0___boxed(lean_object* v_x_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Meta_forEachExpr_x27___redArg___lam__0(v_x_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__1(lean_object* v_inst_451_, lean_object* v_00_u03b1_452_, lean_object* v_x_453_){
_start:
{
lean_object* v___f_454_; lean_object* v___x_455_; 
v___f_454_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_454_, 0, v_x_453_);
v___x_455_ = lean_apply_2(v_inst_451_, lean_box(0), v___f_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__2(lean_object* v_toPure_456_, lean_object* v_____x_457_){
_start:
{
lean_object* v_fst_458_; lean_object* v___x_459_; 
v_fst_458_ = lean_ctor_get(v_____x_457_, 0);
lean_inc(v_fst_458_);
lean_dec_ref(v_____x_457_);
v___x_459_ = lean_apply_2(v_toPure_456_, lean_box(0), v_fst_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__3(lean_object* v_a_460_, lean_object* v_toPure_461_, lean_object* v_s_462_){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v_a_460_);
lean_ctor_set(v___x_463_, 1, v_s_462_);
v___x_464_ = lean_apply_2(v_toPure_461_, lean_box(0), v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__4(lean_object* v_toPure_465_, lean_object* v_ref_466_, lean_object* v_x_467_, lean_object* v_toBind_468_, lean_object* v_a_469_){
_start:
{
lean_object* v___f_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___f_470_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__3), 3, 2);
lean_closure_set(v___f_470_, 0, v_a_469_);
lean_closure_set(v___f_470_, 1, v_toPure_465_);
v___x_471_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_471_, 0, lean_box(0));
lean_closure_set(v___x_471_, 1, lean_box(0));
lean_closure_set(v___x_471_, 2, v_ref_466_);
v___x_472_ = lean_apply_2(v_x_467_, lean_box(0), v___x_471_);
v___x_473_ = lean_apply_4(v_toBind_468_, lean_box(0), lean_box(0), v___x_472_, v___f_470_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__5(lean_object* v_toPure_474_, lean_object* v_x_475_, lean_object* v_toBind_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_fn_479_, lean_object* v_x_480_, lean_object* v_input_481_, lean_object* v_ref_482_){
_start:
{
lean_object* v___f_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
lean_inc(v_toBind_476_);
lean_inc(v_x_475_);
lean_inc(v_ref_482_);
v___f_483_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__4), 5, 4);
lean_closure_set(v___f_483_, 0, v_toPure_474_);
lean_closure_set(v___f_483_, 1, v_ref_482_);
lean_closure_set(v___f_483_, 2, v_x_475_);
lean_closure_set(v___f_483_, 3, v_toBind_476_);
v___x_484_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_477_, v_inst_478_, v_fn_479_, v_x_480_, v_x_475_, v_input_481_, v_ref_482_);
lean_dec(v_ref_482_);
v___x_485_ = lean_apply_4(v_toBind_476_, lean_box(0), lean_box(0), v___x_484_, v___f_483_);
return v___x_485_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_486_; lean_object* v___x_487_; 
v_cellCount_486_ = lean_unsigned_to_nat(16u);
v___x_487_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_486_);
return v___x_487_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_488_; lean_object* v___x_489_; 
v_cellCount_488_ = lean_unsigned_to_nat(16u);
v___x_489_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_488_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__2(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_490_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___redArg___closed__1, &l_Lean_Meta_forEachExpr_x27___redArg___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__1);
v___x_491_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___redArg___closed__0, &l_Lean_Meta_forEachExpr_x27___redArg___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__0);
v___x_492_ = lean_unsigned_to_nat(0u);
v___x_493_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
lean_ctor_set(v___x_493_, 1, v___x_491_);
lean_ctor_set(v___x_493_, 2, v___x_490_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__3(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___redArg___closed__2, &l_Lean_Meta_forEachExpr_x27___redArg___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__2);
v___x_495_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_495_, 0, lean_box(0));
lean_closure_set(v___x_495_, 1, lean_box(0));
lean_closure_set(v___x_495_, 2, v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg(lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_input_499_, lean_object* v_fn_500_){
_start:
{
lean_object* v_x_501_; lean_object* v_toApplicative_502_; lean_object* v_toBind_503_; lean_object* v_toPure_504_; lean_object* v_x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___f_508_; lean_object* v___f_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_x_501_ = lean_box(0);
v_toApplicative_502_ = lean_ctor_get(v_inst_496_, 0);
v_toBind_503_ = lean_ctor_get(v_inst_496_, 1);
lean_inc_n(v_toBind_503_, 3);
v_toPure_504_ = lean_ctor_get(v_toApplicative_502_, 1);
lean_inc_n(v_toPure_504_, 2);
lean_inc(v_inst_497_);
v_x_505_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__1), 3, 1);
lean_closure_set(v_x_505_, 0, v_inst_497_);
v___x_506_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___redArg___closed__3, &l_Lean_Meta_forEachExpr_x27___redArg___closed__3_once, _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__3);
v___x_507_ = l_Lean_Meta_forEachExpr_x27___redArg___lam__1(v_inst_497_, lean_box(0), v___x_506_);
v___f_508_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_508_, 0, v_toPure_504_);
v___f_509_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__5), 9, 8);
lean_closure_set(v___f_509_, 0, v_toPure_504_);
lean_closure_set(v___f_509_, 1, v_x_505_);
lean_closure_set(v___f_509_, 2, v_toBind_503_);
lean_closure_set(v___f_509_, 3, v_inst_496_);
lean_closure_set(v___f_509_, 4, v_inst_498_);
lean_closure_set(v___f_509_, 5, v_fn_500_);
lean_closure_set(v___f_509_, 6, v_x_501_);
lean_closure_set(v___f_509_, 7, v_input_499_);
v___x_510_ = lean_apply_4(v_toBind_503_, lean_box(0), lean_box(0), v___x_507_, v___f_509_);
v___x_511_ = lean_apply_4(v_toBind_503_, lean_box(0), lean_box(0), v___x_510_, v___f_508_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27(lean_object* v_m_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_inst_515_, lean_object* v_input_516_, lean_object* v_fn_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_Meta_forEachExpr_x27___redArg(v_inst_513_, v_inst_514_, v_inst_515_, v_input_516_, v_fn_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg___lam__0(lean_object* v_toPure_519_, lean_object* v_____r_520_){
_start:
{
uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_521_ = 1;
v___x_522_ = lean_box(v___x_521_);
v___x_523_ = lean_apply_2(v_toPure_519_, lean_box(0), v___x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg___lam__1(lean_object* v_f_524_, lean_object* v_toBind_525_, lean_object* v___f_526_, lean_object* v_e_527_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = lean_apply_1(v_f_524_, v_e_527_);
v___x_529_ = lean_apply_4(v_toBind_525_, lean_box(0), lean_box(0), v___x_528_, v___f_526_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg(lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_inst_532_, lean_object* v_e_533_, lean_object* v_f_534_){
_start:
{
lean_object* v_toApplicative_535_; lean_object* v_toBind_536_; lean_object* v_toPure_537_; lean_object* v___f_538_; lean_object* v___f_539_; lean_object* v___x_540_; 
v_toApplicative_535_ = lean_ctor_get(v_inst_530_, 0);
v_toBind_536_ = lean_ctor_get(v_inst_530_, 1);
v_toPure_537_ = lean_ctor_get(v_toApplicative_535_, 1);
lean_inc(v_toPure_537_);
v___f_538_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___redArg___lam__0), 2, 1);
lean_closure_set(v___f_538_, 0, v_toPure_537_);
lean_inc(v_toBind_536_);
v___f_539_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___redArg___lam__1), 4, 3);
lean_closure_set(v___f_539_, 0, v_f_534_);
lean_closure_set(v___f_539_, 1, v_toBind_536_);
lean_closure_set(v___f_539_, 2, v___f_538_);
v___x_540_ = l_Lean_Meta_forEachExpr_x27___redArg(v_inst_530_, v_inst_531_, v_inst_532_, v_e_533_, v___f_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr(lean_object* v_m_541_, lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_e_545_, lean_object* v_f_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_Meta_forEachExpr___redArg(v_inst_542_, v_inst_543_, v_inst_544_, v_e_545_, v_f_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0(lean_object* v_toPure_548_, lean_object* v_____do__lift_549_){
_start:
{
lean_object* v_userName_550_; uint8_t v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_userName_550_ = lean_ctor_get(v_____do__lift_549_, 0);
v___x_551_ = l_Lean_Name_isAnonymous(v_userName_550_);
v___x_552_ = lean_box(v___x_551_);
v___x_553_ = lean_apply_2(v_toPure_548_, lean_box(0), v___x_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0___boxed(lean_object* v_toPure_554_, lean_object* v_____do__lift_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0(v_toPure_554_, v_____do__lift_555_);
lean_dec_ref(v_____do__lift_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg(lean_object* v_inst_557_, lean_object* v_inst_558_, lean_object* v_x_559_){
_start:
{
lean_object* v_toApplicative_560_; 
v_toApplicative_560_ = lean_ctor_get(v_inst_557_, 0);
lean_inc_ref(v_toApplicative_560_);
if (lean_obj_tag(v_x_559_) == 2)
{
lean_object* v_toBind_561_; lean_object* v_toPure_562_; lean_object* v_mvarId_563_; lean_object* v___f_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_toBind_561_ = lean_ctor_get(v_inst_557_, 1);
lean_inc(v_toBind_561_);
lean_dec_ref(v_inst_557_);
v_toPure_562_ = lean_ctor_get(v_toApplicative_560_, 1);
lean_inc(v_toPure_562_);
lean_dec_ref(v_toApplicative_560_);
v_mvarId_563_ = lean_ctor_get(v_x_559_, 0);
lean_inc(v_mvarId_563_);
lean_dec_ref_known(v_x_559_, 1);
v___f_564_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_564_, 0, v_toPure_562_);
v___x_565_ = lean_alloc_closure((void*)(l_Lean_MVarId_getDecl___boxed), 6, 1);
lean_closure_set(v___x_565_, 0, v_mvarId_563_);
v___x_566_ = lean_apply_2(v_inst_558_, lean_box(0), v___x_565_);
v___x_567_ = lean_apply_4(v_toBind_561_, lean_box(0), lean_box(0), v___x_566_, v___f_564_);
return v___x_567_;
}
else
{
lean_object* v_toPure_568_; uint8_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec_ref(v_x_559_);
lean_dec(v_inst_558_);
lean_dec_ref(v_inst_557_);
v_toPure_568_ = lean_ctor_get(v_toApplicative_560_, 1);
lean_inc(v_toPure_568_);
lean_dec_ref(v_toApplicative_560_);
v___x_569_ = 0;
v___x_570_ = lean_box(v___x_569_);
v___x_571_ = lean_apply_2(v_toPure_568_, lean_box(0), v___x_570_);
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName(lean_object* v_m_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_x_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg(v_inst_573_, v_inst_574_, v_x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0(lean_object* v_k_577_, lean_object* v_b_578_, lean_object* v_c_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___x_585_; 
lean_inc(v___y_583_);
lean_inc_ref(v___y_582_);
lean_inc(v___y_581_);
lean_inc_ref(v___y_580_);
v___x_585_ = lean_apply_7(v_k_577_, v_b_578_, v_c_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, lean_box(0));
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0___boxed(lean_object* v_k_586_, lean_object* v_b_587_, lean_object* v_c_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0(v_k_586_, v_b_587_, v_c_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(lean_object* v_type_595_, lean_object* v_maxFVars_x3f_596_, lean_object* v_k_597_, uint8_t v_cleanupAnnotations_598_, uint8_t v_whnfType_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___f_605_; lean_object* v___x_606_; 
v___f_605_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_605_, 0, v_k_597_);
v___x_606_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_595_, v_maxFVars_x3f_596_, v___f_605_, v_cleanupAnnotations_598_, v_whnfType_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
v_a_615_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_606_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_606_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___boxed(lean_object* v_type_623_, lean_object* v_maxFVars_x3f_624_, lean_object* v_k_625_, lean_object* v_cleanupAnnotations_626_, lean_object* v_whnfType_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_633_; uint8_t v_whnfType_boxed_634_; lean_object* v_res_635_; 
v_cleanupAnnotations_boxed_633_ = lean_unbox(v_cleanupAnnotations_626_);
v_whnfType_boxed_634_ = lean_unbox(v_whnfType_627_);
v_res_635_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(v_type_623_, v_maxFVars_x3f_624_, v_k_625_, v_cleanupAnnotations_boxed_633_, v_whnfType_boxed_634_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0(lean_object* v_00_u03b1_636_, lean_object* v_type_637_, lean_object* v_maxFVars_x3f_638_, lean_object* v_k_639_, uint8_t v_cleanupAnnotations_640_, uint8_t v_whnfType_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(v_type_637_, v_maxFVars_x3f_638_, v_k_639_, v_cleanupAnnotations_640_, v_whnfType_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___boxed(lean_object* v_00_u03b1_648_, lean_object* v_type_649_, lean_object* v_maxFVars_x3f_650_, lean_object* v_k_651_, lean_object* v_cleanupAnnotations_652_, lean_object* v_whnfType_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_659_; uint8_t v_whnfType_boxed_660_; lean_object* v_res_661_; 
v_cleanupAnnotations_boxed_659_ = lean_unbox(v_cleanupAnnotations_652_);
v_whnfType_boxed_660_ = lean_unbox(v_whnfType_653_);
v_res_661_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0(v_00_u03b1_648_, v_type_649_, v_maxFVars_x3f_650_, v_k_651_, v_cleanupAnnotations_boxed_659_, v_whnfType_boxed_660_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(lean_object* v_e_662_, lean_object* v___y_663_){
_start:
{
uint8_t v___x_665_; 
v___x_665_ = l_Lean_Expr_hasMVar(v_e_662_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v_e_662_);
return v___x_666_;
}
else
{
lean_object* v___x_667_; lean_object* v_mctx_668_; lean_object* v___x_669_; lean_object* v_fst_670_; lean_object* v_snd_671_; lean_object* v___x_672_; lean_object* v_cache_673_; lean_object* v_zetaDeltaFVarIds_674_; lean_object* v_postponed_675_; lean_object* v_diag_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_685_; 
v___x_667_ = lean_st_ref_get(v___y_663_);
v_mctx_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc_ref(v_mctx_668_);
lean_dec(v___x_667_);
v___x_669_ = l_Lean_instantiateMVarsCore(v_mctx_668_, v_e_662_);
v_fst_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_fst_670_);
v_snd_671_ = lean_ctor_get(v___x_669_, 1);
lean_inc(v_snd_671_);
lean_dec_ref(v___x_669_);
v___x_672_ = lean_st_ref_take(v___y_663_);
v_cache_673_ = lean_ctor_get(v___x_672_, 1);
v_zetaDeltaFVarIds_674_ = lean_ctor_get(v___x_672_, 2);
v_postponed_675_ = lean_ctor_get(v___x_672_, 3);
v_diag_676_ = lean_ctor_get(v___x_672_, 4);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_685_ == 0)
{
lean_object* v_unused_686_; 
v_unused_686_ = lean_ctor_get(v___x_672_, 0);
lean_dec(v_unused_686_);
v___x_678_ = v___x_672_;
v_isShared_679_ = v_isSharedCheck_685_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_diag_676_);
lean_inc(v_postponed_675_);
lean_inc(v_zetaDeltaFVarIds_674_);
lean_inc(v_cache_673_);
lean_dec(v___x_672_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_685_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v_snd_671_);
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_snd_671_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_cache_673_);
lean_ctor_set(v_reuseFailAlloc_684_, 2, v_zetaDeltaFVarIds_674_);
lean_ctor_set(v_reuseFailAlloc_684_, 3, v_postponed_675_);
lean_ctor_set(v_reuseFailAlloc_684_, 4, v_diag_676_);
v___x_681_ = v_reuseFailAlloc_684_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_st_ref_put(v___y_663_, v___x_681_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v_fst_670_);
return v___x_683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg___boxed(lean_object* v_e_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(v_e_687_, v___y_688_);
lean_dec(v___y_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3(lean_object* v_e_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(v_e_691_, v___y_693_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___boxed(lean_object* v_e_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3(v_e_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0(lean_object* v_a_705_, lean_object* v___x_706_, lean_object* v_val_707_, lean_object* v___x_708_, lean_object* v_xs_709_, lean_object* v_x_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = lean_array_get_size(v_xs_709_);
v___x_717_ = lean_nat_dec_lt(v_a_705_, v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; 
lean_dec(v___x_708_);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_706_);
return v___x_718_;
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_719_ = l_Lean_instInhabitedExpr;
v___x_720_ = lean_array_get_borrowed(v___x_719_, v_xs_709_, v_a_705_);
v___x_721_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_720_, v___y_711_, v___y_713_, v___y_714_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
v___x_723_ = l_Lean_LocalDecl_userName(v_a_722_);
lean_dec(v_a_722_);
v___x_724_ = l_Lean_Core_mkFreshUserName(v___x_723_, v___y_713_, v___y_714_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_750_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_750_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_750_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_750_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v_mctx_733_; lean_object* v_cache_734_; lean_object* v_zetaDeltaFVarIds_735_; lean_object* v_postponed_736_; lean_object* v_diag_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_749_; 
v___x_729_ = lean_st_ref_take(v_val_707_);
lean_inc(v___x_708_);
v___x_730_ = lean_array_push(v___x_729_, v___x_708_);
v___x_731_ = lean_st_ref_put(v_val_707_, v___x_730_);
v___x_732_ = lean_st_ref_take(v___y_712_);
v_mctx_733_ = lean_ctor_get(v___x_732_, 0);
v_cache_734_ = lean_ctor_get(v___x_732_, 1);
v_zetaDeltaFVarIds_735_ = lean_ctor_get(v___x_732_, 2);
v_postponed_736_ = lean_ctor_get(v___x_732_, 3);
v_diag_737_ = lean_ctor_get(v___x_732_, 4);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_749_ == 0)
{
v___x_739_ = v___x_732_;
v_isShared_740_ = v_isSharedCheck_749_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_diag_737_);
lean_inc(v_postponed_736_);
lean_inc(v_zetaDeltaFVarIds_735_);
lean_inc(v_cache_734_);
lean_inc(v_mctx_733_);
lean_dec(v___x_732_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_749_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_741_ = l_Lean_MetavarContext_setMVarUserNameTemporarily(v_mctx_733_, v___x_708_, v_a_725_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_741_);
v___x_743_ = v___x_739_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_cache_734_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_zetaDeltaFVarIds_735_);
lean_ctor_set(v_reuseFailAlloc_748_, 3, v_postponed_736_);
lean_ctor_set(v_reuseFailAlloc_748_, 4, v_diag_737_);
v___x_743_ = v_reuseFailAlloc_748_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_744_ = lean_st_ref_put(v___y_712_, v___x_743_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_706_);
v___x_746_ = v___x_727_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_706_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec(v___x_708_);
v_a_751_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_724_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_724_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec(v___x_708_);
v_a_759_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_721_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_721_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0___boxed(lean_object* v_a_767_, lean_object* v___x_768_, lean_object* v_val_769_, lean_object* v___x_770_, lean_object* v_xs_771_, lean_object* v_x_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0(v_a_767_, v___x_768_, v_val_769_, v___x_770_, v_xs_771_, v_x_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec_ref(v_x_772_);
lean_dec_ref(v_xs_771_);
lean_dec(v_val_769_);
lean_dec(v_a_767_);
return v_res_778_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(lean_object* v_a_779_, lean_object* v_as_780_, size_t v_i_781_, size_t v_stop_782_){
_start:
{
uint8_t v___x_783_; 
v___x_783_ = lean_usize_dec_eq(v_i_781_, v_stop_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_784_ = lean_array_uget_borrowed(v_as_780_, v_i_781_);
v___x_785_ = lean_expr_eqv(v_a_779_, v___x_784_);
if (v___x_785_ == 0)
{
size_t v___x_786_; size_t v___x_787_; 
v___x_786_ = ((size_t)1ULL);
v___x_787_ = lean_usize_add(v_i_781_, v___x_786_);
v_i_781_ = v___x_787_;
goto _start;
}
else
{
return v___x_785_;
}
}
else
{
uint8_t v___x_789_; 
v___x_789_ = 0;
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1___boxed(lean_object* v_a_790_, lean_object* v_as_791_, lean_object* v_i_792_, lean_object* v_stop_793_){
_start:
{
size_t v_i_boxed_794_; size_t v_stop_boxed_795_; uint8_t v_res_796_; lean_object* v_r_797_; 
v_i_boxed_794_ = lean_unbox_usize(v_i_792_);
lean_dec(v_i_792_);
v_stop_boxed_795_ = lean_unbox_usize(v_stop_793_);
lean_dec(v_stop_793_);
v_res_796_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(v_a_790_, v_as_791_, v_i_boxed_794_, v_stop_boxed_795_);
lean_dec_ref(v_as_791_);
lean_dec_ref(v_a_790_);
v_r_797_ = lean_box(v_res_796_);
return v_r_797_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(lean_object* v_as_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_array_get_size(v_as_798_);
v___x_802_ = lean_nat_dec_lt(v___x_800_, v___x_801_);
if (v___x_802_ == 0)
{
return v___x_802_;
}
else
{
if (v___x_802_ == 0)
{
return v___x_802_;
}
else
{
size_t v___x_803_; size_t v___x_804_; uint8_t v___x_805_; 
v___x_803_ = ((size_t)0ULL);
v___x_804_ = lean_usize_of_nat(v___x_801_);
v___x_805_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(v_a_799_, v_as_798_, v___x_803_, v___x_804_);
return v___x_805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1___boxed(lean_object* v_as_806_, lean_object* v_a_807_){
_start:
{
uint8_t v_res_808_; lean_object* v_r_809_; 
v_res_808_ = l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(v_as_806_, v_a_807_);
lean_dec_ref(v_a_807_);
lean_dec_ref(v_as_806_);
v_r_809_ = lean_box(v_res_808_);
return v_r_809_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(lean_object* v_upperBound_810_, lean_object* v___x_811_, lean_object* v_val_812_, lean_object* v_e_813_, lean_object* v_isTarget_814_, lean_object* v_a_815_, lean_object* v_b_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_a_823_; uint8_t v___x_827_; 
v___x_827_ = lean_nat_dec_lt(v_a_815_, v_upperBound_810_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
lean_dec(v_a_815_);
lean_dec(v_val_812_);
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v_b_816_);
return v___x_828_;
}
else
{
lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___y_832_; uint8_t v___x_863_; 
v___x_829_ = lean_box(0);
v___x_830_ = lean_array_fget_borrowed(v___x_811_, v_a_815_);
v___x_863_ = l_Lean_Expr_isMVar(v___x_830_);
if (v___x_863_ == 0)
{
v___y_832_ = v___x_863_;
goto v___jp_831_;
}
else
{
uint8_t v___x_864_; 
v___x_864_ = l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(v_isTarget_814_, v___x_830_);
v___y_832_ = v___x_864_;
goto v___jp_831_;
}
v___jp_831_:
{
if (v___y_832_ == 0)
{
v_a_823_ = v___x_829_;
goto v___jp_822_;
}
else
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = l_Lean_Expr_mvarId_x21(v___x_830_);
lean_inc(v___x_833_);
v___x_834_ = l_Lean_MVarId_getDecl(v___x_833_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v_userName_836_; uint8_t v___x_837_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_835_);
lean_dec_ref_known(v___x_834_, 1);
v_userName_836_ = lean_ctor_get(v_a_835_, 0);
lean_inc(v_userName_836_);
lean_dec(v_a_835_);
v___x_837_ = l_Lean_Name_isAnonymous(v_userName_836_);
lean_dec(v_userName_836_);
if (v___x_837_ == 0)
{
lean_dec(v___x_833_);
v_a_823_ = v___x_829_;
goto v___jp_822_;
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = l_Lean_Expr_getAppFn(v_e_813_);
lean_inc(v___y_820_);
lean_inc_ref(v___y_819_);
lean_inc(v___y_818_);
lean_inc_ref(v___y_817_);
v___x_839_ = lean_infer_type(v___x_838_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___f_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; uint8_t v___x_845_; lean_object* v___x_846_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
lean_inc(v_val_812_);
lean_inc(v_a_815_);
v___f_841_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_841_, 0, v_a_815_);
lean_closure_set(v___f_841_, 1, v___x_829_);
lean_closure_set(v___f_841_, 2, v_val_812_);
lean_closure_set(v___f_841_, 3, v___x_833_);
v___x_842_ = lean_unsigned_to_nat(1u);
v___x_843_ = lean_nat_add(v_a_815_, v___x_842_);
v___x_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
v___x_845_ = 0;
v___x_846_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(v_a_840_, v___x_844_, v___f_841_, v___x_845_, v___x_845_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_dec_ref_known(v___x_846_, 1);
v_a_823_ = v___x_829_;
goto v___jp_822_;
}
else
{
lean_dec(v_a_815_);
lean_dec(v_val_812_);
return v___x_846_;
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec(v___x_833_);
lean_dec(v_a_815_);
lean_dec(v_val_812_);
v_a_847_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_839_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_839_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec(v___x_833_);
lean_dec(v_a_815_);
lean_dec(v_val_812_);
v_a_855_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_834_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_834_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
}
v___jp_822_:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_unsigned_to_nat(1u);
v___x_825_ = lean_nat_add(v_a_815_, v___x_824_);
lean_dec(v_a_815_);
v_a_815_ = v___x_825_;
v_b_816_ = v_a_823_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___boxed(lean_object* v_upperBound_865_, lean_object* v___x_866_, lean_object* v_val_867_, lean_object* v_e_868_, lean_object* v_isTarget_869_, lean_object* v_a_870_, lean_object* v_b_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(v_upperBound_865_, v___x_866_, v_val_867_, v_e_868_, v_isTarget_869_, v_a_870_, v_b_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec_ref(v_isTarget_869_);
lean_dec_ref(v_e_868_);
lean_dec_ref(v___x_866_);
lean_dec(v_upperBound_865_);
return v_res_877_;
}
}
static lean_object* _init_l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0(void){
_start:
{
lean_object* v___x_878_; lean_object* v_dummy_879_; 
v___x_878_ = lean_box(0);
v_dummy_879_ = l_Lean_Expr_sort___override(v___x_878_);
return v_dummy_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___lam__0(lean_object* v_val_880_, lean_object* v_isTarget_881_, lean_object* v___x_882_, lean_object* v_e_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
uint8_t v___x_889_; 
v___x_889_ = l_Lean_Expr_isApp(v_e_883_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; lean_object* v___x_891_; 
lean_dec_ref(v_e_883_);
lean_dec(v___x_882_);
lean_dec(v_val_880_);
v___x_890_ = lean_box(0);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
else
{
lean_object* v_dummy_892_; lean_object* v_nargs_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_dummy_892_ = lean_obj_once(&l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0, &l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0_once, _init_l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0);
v_nargs_893_ = l_Lean_Expr_getAppNumArgs(v_e_883_);
lean_inc(v_nargs_893_);
v___x_894_ = lean_mk_array(v_nargs_893_, v_dummy_892_);
v___x_895_ = lean_unsigned_to_nat(1u);
v___x_896_ = lean_nat_sub(v_nargs_893_, v___x_895_);
lean_dec(v_nargs_893_);
lean_inc_ref(v_e_883_);
v___x_897_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_883_, v___x_894_, v___x_896_);
v___x_898_ = lean_array_get_size(v___x_897_);
v___x_899_ = lean_box(0);
v___x_900_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(v___x_898_, v___x_897_, v_val_880_, v_e_883_, v_isTarget_881_, v___x_882_, v___x_899_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec_ref(v_e_883_);
lean_dec_ref(v___x_897_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; 
v_unused_908_ = lean_ctor_get(v___x_900_, 0);
lean_dec(v_unused_908_);
v___x_902_ = v___x_900_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_dec(v___x_900_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v___x_899_);
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_899_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
else
{
return v___x_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___lam__0___boxed(lean_object* v_val_909_, lean_object* v_isTarget_910_, lean_object* v___x_911_, lean_object* v_e_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_Meta_setMVarUserNamesAt___lam__0(v_val_909_, v_isTarget_910_, v___x_911_, v_e_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec_ref(v_isTarget_910_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_object* v_00_u03b1_919_, lean_object* v_x_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = lean_apply_1(v_x_920_, lean_box(0));
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0___boxed(lean_object* v_00_u03b1_928_, lean_object* v_x_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(v_00_u03b1_928_, v_x_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(lean_object* v_m_936_, lean_object* v_query_937_, lean_object* v_x_938_, lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
lean_object* v_zero_941_; uint8_t v_isZero_942_; 
v_zero_941_ = lean_unsigned_to_nat(0u);
v_isZero_942_ = lean_nat_dec_eq(v_x_939_, v_zero_941_);
if (v_isZero_942_ == 1)
{
lean_dec(v_x_940_);
lean_dec(v_x_939_);
if (lean_obj_tag(v_x_938_) == 0)
{
lean_object* v___x_943_; 
v___x_943_ = lean_box(2);
return v___x_943_;
}
else
{
lean_object* v_val_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
v_val_944_ = lean_ctor_get(v_x_938_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v_x_938_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v_x_938_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_val_944_);
lean_dec(v_x_938_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_val_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
else
{
lean_object* v_keyArray_952_; lean_object* v_valueArray_953_; lean_object* v___x_954_; uint8_t v_isSome_955_; 
v_keyArray_952_ = lean_ctor_get(v_m_936_, 1);
v_valueArray_953_ = lean_ctor_get(v_m_936_, 2);
v___x_954_ = lean_array_fget_borrowed(v_keyArray_952_, v_x_940_);
v_isSome_955_ = lean_noption_is_some(v___x_954_);
if (v_isSome_955_ == 0)
{
lean_dec(v_x_939_);
if (lean_obj_tag(v_x_938_) == 0)
{
lean_object* v___x_956_; 
v___x_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_956_, 0, v_x_940_);
return v___x_956_;
}
else
{
lean_object* v_val_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_dec(v_x_940_);
v_val_957_ = lean_ctor_get(v_x_938_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v_x_938_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v_x_938_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_val_957_);
lean_dec(v_x_938_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_val_957_);
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
else
{
lean_object* v_one_965_; lean_object* v_n_966_; lean_object* v___y_968_; 
v_one_965_ = lean_unsigned_to_nat(1u);
v_n_966_ = lean_nat_sub(v_x_939_, v_one_965_);
lean_dec(v_x_939_);
if (v_isSome_955_ == 0)
{
goto v___jp_974_;
}
else
{
lean_object* v___x_976_; uint8_t v_isSome_977_; 
v___x_976_ = lean_array_fget_borrowed(v_valueArray_953_, v_x_940_);
v_isSome_977_ = lean_noption_is_some(v___x_976_);
if (v_isSome_977_ == 0)
{
goto v___jp_974_;
}
else
{
lean_object* v_val_978_; uint8_t v___x_979_; 
lean_inc(v___x_954_);
v_val_978_ = lean_noption_get(v___x_954_);
v___x_979_ = lean_expr_eqv(v_val_978_, v_query_937_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
lean_dec(v_val_978_);
v___x_980_ = lean_array_get_size(v_keyArray_952_);
v___x_981_ = lean_nat_add(v_x_940_, v_one_965_);
lean_dec(v_x_940_);
v___x_982_ = lean_nat_dec_lt(v___x_981_, v___x_980_);
if (v___x_982_ == 0)
{
lean_dec(v___x_981_);
v_x_939_ = v_n_966_;
v_x_940_ = v_zero_941_;
goto _start;
}
else
{
v_x_939_ = v_n_966_;
v_x_940_ = v___x_981_;
goto _start;
}
}
else
{
lean_object* v_val_985_; lean_object* v___x_986_; 
lean_dec(v_n_966_);
lean_dec(v_x_938_);
lean_inc(v___x_976_);
v_val_985_ = lean_noption_get(v___x_976_);
v___x_986_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_986_, 0, v_x_940_);
lean_ctor_set(v___x_986_, 1, v_val_978_);
lean_ctor_set(v___x_986_, 2, v_val_985_);
return v___x_986_;
}
}
}
v___jp_967_:
{
lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_969_ = lean_array_get_size(v_keyArray_952_);
v___x_970_ = lean_nat_add(v_x_940_, v_one_965_);
lean_dec(v_x_940_);
v___x_971_ = lean_nat_dec_lt(v___x_970_, v___x_969_);
if (v___x_971_ == 0)
{
lean_dec(v___x_970_);
v_x_938_ = v___y_968_;
v_x_939_ = v_n_966_;
v_x_940_ = v_zero_941_;
goto _start;
}
else
{
v_x_938_ = v___y_968_;
v_x_939_ = v_n_966_;
v_x_940_ = v___x_970_;
goto _start;
}
}
v___jp_974_:
{
if (lean_obj_tag(v_x_938_) == 0)
{
lean_object* v___x_975_; 
lean_inc(v_x_940_);
v___x_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_975_, 0, v_x_940_);
v___y_968_ = v___x_975_;
goto v___jp_967_;
}
else
{
v___y_968_ = v_x_938_;
goto v___jp_967_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_m_987_, lean_object* v_query_988_, lean_object* v_x_989_, lean_object* v_x_990_, lean_object* v_x_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_m_987_, v_query_988_, v_x_989_, v_x_990_, v_x_991_);
lean_dec_ref(v_query_988_);
lean_dec_ref(v_m_987_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(lean_object* v_m_993_, lean_object* v_query_994_){
_start:
{
lean_object* v_keyArray_995_; lean_object* v___x_996_; uint64_t v___x_997_; uint64_t v___x_998_; uint64_t v___x_999_; uint64_t v_fold_1000_; uint64_t v___x_1001_; uint64_t v___x_1002_; uint64_t v___x_1003_; size_t v___x_1004_; size_t v___x_1005_; size_t v___x_1006_; size_t v___x_1007_; size_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v_keyArray_995_ = lean_ctor_get(v_m_993_, 1);
v___x_996_ = lean_array_get_size(v_keyArray_995_);
v___x_997_ = l_Lean_Expr_hash(v_query_994_);
v___x_998_ = 32ULL;
v___x_999_ = lean_uint64_shift_right(v___x_997_, v___x_998_);
v_fold_1000_ = lean_uint64_xor(v___x_997_, v___x_999_);
v___x_1001_ = 16ULL;
v___x_1002_ = lean_uint64_shift_right(v_fold_1000_, v___x_1001_);
v___x_1003_ = lean_uint64_xor(v_fold_1000_, v___x_1002_);
v___x_1004_ = lean_uint64_to_usize(v___x_1003_);
v___x_1005_ = lean_usize_of_nat(v___x_996_);
v___x_1006_ = ((size_t)1ULL);
v___x_1007_ = lean_usize_sub(v___x_1005_, v___x_1006_);
v___x_1008_ = lean_usize_land(v___x_1004_, v___x_1007_);
v___x_1009_ = lean_usize_to_nat(v___x_1008_);
v___x_1010_ = lean_box(0);
v___x_1011_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_m_993_, v_query_994_, v___x_1010_, v___x_996_, v___x_1009_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_m_1012_, lean_object* v_query_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(v_m_1012_, v_query_1013_);
lean_dec_ref(v_query_1013_);
lean_dec_ref(v_m_1012_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_m_1015_, lean_object* v_query_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(v_m_1015_, v_query_1016_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_index_1018_; lean_object* v_key_1019_; lean_object* v_value_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
v_index_1018_ = lean_ctor_get(v___x_1017_, 0);
v_key_1019_ = lean_ctor_get(v___x_1017_, 1);
v_value_1020_ = lean_ctor_get(v___x_1017_, 2);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1017_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_value_1020_);
lean_inc(v_key_1019_);
lean_inc(v_index_1018_);
lean_dec(v___x_1017_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_index_1018_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_key_1019_);
lean_ctor_set(v_reuseFailAlloc_1026_, 2, v_value_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
else
{
lean_object* v___x_1028_; 
lean_dec(v___x_1017_);
v___x_1028_ = lean_box(1);
return v___x_1028_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_m_1029_, lean_object* v_query_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(v_m_1029_, v_query_1030_);
lean_dec_ref(v_query_1030_);
lean_dec_ref(v_m_1029_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_m_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(v_m_1032_, v_a_1033_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_value_1035_; lean_object* v___x_1036_; 
v_value_1035_ = lean_ctor_get(v___x_1034_, 2);
lean_inc(v_value_1035_);
lean_dec_ref_known(v___x_1034_, 3);
v___x_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1036_, 0, v_value_1035_);
return v___x_1036_;
}
else
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_box(0);
return v___x_1037_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_m_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_m_1038_, v_a_1039_);
lean_dec_ref(v_a_1039_);
lean_dec_ref(v_m_1038_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12_spec__13___redArg(lean_object* v_b_1041_, lean_object* v_acc_1042_, lean_object* v_i_1043_){
_start:
{
lean_object* v___y_1045_; lean_object* v_keyArray_1053_; lean_object* v_valueArray_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v_keyArray_1053_ = lean_ctor_get(v_b_1041_, 1);
v_valueArray_1054_ = lean_ctor_get(v_b_1041_, 2);
v___x_1055_ = lean_array_get_size(v_keyArray_1053_);
v___x_1056_ = lean_nat_dec_lt(v_i_1043_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_dec(v_i_1043_);
return v_acc_1042_;
}
else
{
lean_object* v___x_1057_; uint8_t v_isSome_1058_; 
v___x_1057_ = lean_array_fget_borrowed(v_keyArray_1053_, v_i_1043_);
v_isSome_1058_ = lean_noption_is_some(v___x_1057_);
if (v_isSome_1058_ == 0)
{
goto v___jp_1049_;
}
else
{
lean_object* v___x_1059_; uint8_t v_isSome_1060_; 
v___x_1059_ = lean_array_fget_borrowed(v_valueArray_1054_, v_i_1043_);
v_isSome_1060_ = lean_noption_is_some(v___x_1059_);
if (v_isSome_1060_ == 0)
{
goto v___jp_1049_;
}
else
{
lean_object* v_val_1061_; lean_object* v_val_1062_; lean_object* v_i_1064_; lean_object* v___x_1069_; 
lean_inc(v___x_1057_);
v_val_1061_ = lean_noption_get(v___x_1057_);
lean_inc(v___x_1059_);
v_val_1062_ = lean_noption_get(v___x_1059_);
v___x_1069_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(v_acc_1042_, v_val_1061_);
switch(lean_obj_tag(v___x_1069_))
{
case 0:
{
lean_object* v_index_1070_; lean_object* v_size_1071_; lean_object* v___x_1072_; 
v_index_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_index_1070_);
lean_dec_ref_known(v___x_1069_, 3);
v_size_1071_ = lean_ctor_get(v_acc_1042_, 0);
lean_inc(v_size_1071_);
v___x_1072_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1042_, v_size_1071_, v_index_1070_, v_val_1061_, v_val_1062_);
lean_dec(v_index_1070_);
v___y_1045_ = v___x_1072_;
goto v___jp_1044_;
}
case 1:
{
lean_object* v_index_1073_; 
v_index_1073_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_index_1073_);
lean_dec_ref_known(v___x_1069_, 1);
v_i_1064_ = v_index_1073_;
goto v___jp_1063_;
}
default: 
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_1042_, v___x_1074_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_index_1076_; 
v_index_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_index_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v_i_1064_ = v_index_1076_;
goto v___jp_1063_;
}
else
{
lean_dec(v_val_1062_);
lean_dec(v_val_1061_);
v___y_1045_ = v_acc_1042_;
goto v___jp_1044_;
}
}
}
v___jp_1063_:
{
lean_object* v_size_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_size_1065_ = lean_ctor_get(v_acc_1042_, 0);
v___x_1066_ = lean_unsigned_to_nat(1u);
v___x_1067_ = lean_nat_add(v_size_1065_, v___x_1066_);
v___x_1068_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1042_, v___x_1067_, v_i_1064_, v_val_1061_, v_val_1062_);
lean_dec(v_i_1064_);
v___y_1045_ = v___x_1068_;
goto v___jp_1044_;
}
}
}
}
v___jp_1044_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_unsigned_to_nat(1u);
v___x_1047_ = lean_nat_add(v_i_1043_, v___x_1046_);
lean_dec(v_i_1043_);
v_acc_1042_ = v___y_1045_;
v_i_1043_ = v___x_1047_;
goto _start;
}
v___jp_1049_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_unsigned_to_nat(1u);
v___x_1051_ = lean_nat_add(v_i_1043_, v___x_1050_);
lean_dec(v_i_1043_);
v_i_1043_ = v___x_1051_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12_spec__13___redArg___boxed(lean_object* v_b_1077_, lean_object* v_acc_1078_, lean_object* v_i_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12_spec__13___redArg(v_b_1077_, v_acc_1078_, v_i_1079_);
lean_dec_ref(v_b_1077_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12___redArg(lean_object* v_init_1081_, lean_object* v_b_1082_){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12_spec__13___redArg(v_b_1082_, v_init_1081_, v___x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12___redArg___boxed(lean_object* v_init_1085_, lean_object* v_b_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12___redArg(v_init_1085_, v_b_1086_);
lean_dec_ref(v_b_1086_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9___redArg(lean_object* v_m_1088_){
_start:
{
lean_object* v_keyArray_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v_cellCount_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v_target_1096_; lean_object* v___x_1097_; 
v_keyArray_1089_ = lean_ctor_get(v_m_1088_, 1);
v___x_1090_ = lean_array_get_size(v_keyArray_1089_);
v___x_1091_ = lean_unsigned_to_nat(2u);
v_cellCount_1092_ = lean_nat_mul(v___x_1090_, v___x_1091_);
v___x_1093_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1092_);
v___x_1094_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1092_);
v___x_1095_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1092_);
v_target_1096_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1096_, 0, v___x_1093_);
lean_ctor_set(v_target_1096_, 1, v___x_1094_);
lean_ctor_set(v_target_1096_, 2, v___x_1095_);
v___x_1097_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12___redArg(v_target_1096_, v_m_1088_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9___redArg___boxed(lean_object* v_m_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9___redArg(v_m_1098_);
lean_dec_ref(v_m_1098_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1(lean_object* v_a_1100_, lean_object* v_e_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___y_1107_; lean_object* v___y_1110_; lean_object* v_i_1111_; lean_object* v___y_1127_; lean_object* v_i_1128_; lean_object* v___y_1134_; lean_object* v___x_1143_; 
v___x_1104_ = lean_st_ref_take(v_a_1100_);
v___x_1105_ = lean_box(0);
v___x_1143_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(v___x_1104_, v_e_1101_);
switch(lean_obj_tag(v___x_1143_))
{
case 0:
{
lean_object* v_index_1144_; lean_object* v_size_1145_; lean_object* v___x_1146_; 
v_index_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_index_1144_);
lean_dec_ref_known(v___x_1143_, 3);
v_size_1145_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_size_1145_);
v___x_1146_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1104_, v_size_1145_, v_index_1144_, v_e_1101_, v_a_1102_);
lean_dec(v_index_1144_);
v___y_1107_ = v___x_1146_;
goto v___jp_1106_;
}
case 1:
{
lean_object* v_index_1147_; lean_object* v_size_1148_; lean_object* v_keyArray_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v_index_1147_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_index_1147_);
lean_dec_ref_known(v___x_1143_, 1);
v_size_1148_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_size_1148_);
v_keyArray_1149_ = lean_ctor_get(v___x_1104_, 1);
lean_inc_ref(v_keyArray_1149_);
v___x_1150_ = lean_unsigned_to_nat(1u);
v___x_1151_ = lean_nat_add(v_size_1148_, v___x_1150_);
lean_dec(v_size_1148_);
v___x_1152_ = lean_array_get_size(v_keyArray_1149_);
lean_dec_ref(v_keyArray_1149_);
v___x_1153_ = lean_nat_dec_lt(v___x_1151_, v___x_1152_);
if (v___x_1153_ == 0)
{
lean_dec(v___x_1151_);
lean_dec(v_index_1147_);
goto v___jp_1116_;
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1154_ = lean_unsigned_to_nat(4u);
v___x_1155_ = lean_nat_mul(v___x_1151_, v___x_1154_);
v___x_1156_ = lean_unsigned_to_nat(3u);
v___x_1157_ = lean_nat_mul(v___x_1152_, v___x_1156_);
v___x_1158_ = lean_nat_dec_le(v___x_1155_, v___x_1157_);
lean_dec(v___x_1157_);
lean_dec(v___x_1155_);
if (v___x_1158_ == 0)
{
lean_dec(v___x_1151_);
lean_dec(v_index_1147_);
goto v___jp_1116_;
}
else
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1104_, v___x_1151_, v_index_1147_, v_e_1101_, v_a_1102_);
lean_dec(v_index_1147_);
v___y_1107_ = v___x_1159_;
goto v___jp_1106_;
}
}
}
default: 
{
lean_object* v_size_1160_; lean_object* v_keyArray_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v_size_1160_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_size_1160_);
v_keyArray_1161_ = lean_ctor_get(v___x_1104_, 1);
lean_inc_ref(v_keyArray_1161_);
v___x_1162_ = lean_unsigned_to_nat(1u);
v___x_1163_ = lean_nat_add(v_size_1160_, v___x_1162_);
lean_dec(v_size_1160_);
v___x_1164_ = lean_array_get_size(v_keyArray_1161_);
lean_dec_ref(v_keyArray_1161_);
v___x_1165_ = lean_nat_dec_lt(v___x_1163_, v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; 
lean_dec(v___x_1163_);
v___x_1166_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9___redArg(v___x_1104_);
lean_dec(v___x_1104_);
v___y_1134_ = v___x_1166_;
goto v___jp_1133_;
}
else
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1167_ = lean_unsigned_to_nat(4u);
v___x_1168_ = lean_nat_mul(v___x_1163_, v___x_1167_);
lean_dec(v___x_1163_);
v___x_1169_ = lean_unsigned_to_nat(3u);
v___x_1170_ = lean_nat_mul(v___x_1164_, v___x_1169_);
v___x_1171_ = lean_nat_dec_le(v___x_1168_, v___x_1170_);
lean_dec(v___x_1170_);
lean_dec(v___x_1168_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9___redArg(v___x_1104_);
lean_dec(v___x_1104_);
v___y_1134_ = v___x_1172_;
goto v___jp_1133_;
}
else
{
v___y_1134_ = v___x_1104_;
goto v___jp_1133_;
}
}
}
}
v___jp_1106_:
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_st_ref_put(v_a_1100_, v___y_1107_);
return v___x_1105_;
}
v___jp_1109_:
{
lean_object* v_size_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v_size_1112_ = lean_ctor_get(v___y_1110_, 0);
v___x_1113_ = lean_unsigned_to_nat(1u);
v___x_1114_ = lean_nat_add(v_size_1112_, v___x_1113_);
v___x_1115_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1110_, v___x_1114_, v_i_1111_, v_e_1101_, v_a_1102_);
lean_dec(v_i_1111_);
v___y_1107_ = v___x_1115_;
goto v___jp_1106_;
}
v___jp_1116_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9___redArg(v___x_1104_);
lean_dec(v___x_1104_);
v___x_1118_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(v___x_1117_, v_e_1101_);
switch(lean_obj_tag(v___x_1118_))
{
case 0:
{
lean_object* v_index_1119_; lean_object* v_size_1120_; lean_object* v___x_1121_; 
v_index_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_index_1119_);
lean_dec_ref_known(v___x_1118_, 3);
v_size_1120_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_size_1120_);
v___x_1121_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1117_, v_size_1120_, v_index_1119_, v_e_1101_, v_a_1102_);
lean_dec(v_index_1119_);
v___y_1107_ = v___x_1121_;
goto v___jp_1106_;
}
case 1:
{
lean_object* v_index_1122_; 
v_index_1122_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_index_1122_);
lean_dec_ref_known(v___x_1118_, 1);
v___y_1110_ = v___x_1117_;
v_i_1111_ = v_index_1122_;
goto v___jp_1109_;
}
default: 
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1117_, v___x_1123_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_index_1125_; 
v_index_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_index_1125_);
lean_dec_ref_known(v___x_1124_, 1);
v___y_1110_ = v___x_1117_;
v_i_1111_ = v_index_1125_;
goto v___jp_1109_;
}
else
{
lean_dec_ref(v_e_1101_);
v___y_1107_ = v___x_1117_;
goto v___jp_1106_;
}
}
}
}
v___jp_1126_:
{
lean_object* v_size_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v_size_1129_ = lean_ctor_get(v___y_1127_, 0);
v___x_1130_ = lean_unsigned_to_nat(1u);
v___x_1131_ = lean_nat_add(v_size_1129_, v___x_1130_);
v___x_1132_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1127_, v___x_1131_, v_i_1128_, v_e_1101_, v_a_1102_);
lean_dec(v_i_1128_);
v___y_1107_ = v___x_1132_;
goto v___jp_1106_;
}
v___jp_1133_:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(v___y_1134_, v_e_1101_);
switch(lean_obj_tag(v___x_1135_))
{
case 0:
{
lean_object* v_index_1136_; lean_object* v_size_1137_; lean_object* v___x_1138_; 
v_index_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_index_1136_);
lean_dec_ref_known(v___x_1135_, 3);
v_size_1137_ = lean_ctor_get(v___y_1134_, 0);
lean_inc(v_size_1137_);
v___x_1138_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1134_, v_size_1137_, v_index_1136_, v_e_1101_, v_a_1102_);
lean_dec(v_index_1136_);
v___y_1107_ = v___x_1138_;
goto v___jp_1106_;
}
case 1:
{
lean_object* v_index_1139_; 
v_index_1139_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_index_1139_);
lean_dec_ref_known(v___x_1135_, 1);
v___y_1127_ = v___y_1134_;
v_i_1128_ = v_index_1139_;
goto v___jp_1126_;
}
default: 
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1134_, v___x_1140_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_index_1142_; 
v_index_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_index_1142_);
lean_dec_ref_known(v___x_1141_, 1);
v___y_1127_ = v___y_1134_;
v_i_1128_ = v_index_1142_;
goto v___jp_1126_;
}
else
{
lean_dec_ref(v_e_1101_);
v___y_1107_ = v___y_1134_;
goto v___jp_1106_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_a_1173_, lean_object* v_e_1174_, lean_object* v_a_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1(v_a_1173_, v_e_1174_, v_a_1175_);
lean_dec(v_a_1173_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16___redArg___lam__0(lean_object* v_k_1178_, lean_object* v___y_1179_, lean_object* v_b_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1186_; 
lean_inc(v___y_1184_);
lean_inc_ref(v___y_1183_);
lean_inc(v___y_1182_);
lean_inc_ref(v___y_1181_);
lean_inc(v___y_1179_);
v___x_1186_ = lean_apply_7(v_k_1178_, v_b_1180_, v___y_1179_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, lean_box(0));
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16___redArg___lam__0___boxed(lean_object* v_k_1187_, lean_object* v___y_1188_, lean_object* v_b_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16___redArg___lam__0(v_k_1187_, v___y_1188_, v_b_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1188_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16___redArg(lean_object* v_name_1196_, uint8_t v_bi_1197_, lean_object* v_type_1198_, lean_object* v_k_1199_, uint8_t v_kind_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v___f_1207_; lean_object* v___x_1208_; 
lean_inc(v___y_1201_);
v___f_1207_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1207_, 0, v_k_1199_);
lean_closure_set(v___f_1207_, 1, v___y_1201_);
v___x_1208_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1196_, v_bi_1197_, v_type_1198_, v___f_1207_, v_kind_1200_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
if (lean_obj_tag(v___x_1208_) == 0)
{
return v___x_1208_;
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1208_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1208_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16___redArg___boxed(lean_object* v_name_1217_, lean_object* v_bi_1218_, lean_object* v_type_1219_, lean_object* v_k_1220_, lean_object* v_kind_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
uint8_t v_bi_boxed_1228_; uint8_t v_kind_boxed_1229_; lean_object* v_res_1230_; 
v_bi_boxed_1228_ = lean_unbox(v_bi_1218_);
v_kind_boxed_1229_ = lean_unbox(v_kind_1221_);
v_res_1230_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16___redArg(v_name_1217_, v_bi_boxed_1228_, v_type_1219_, v_k_1220_, v_kind_boxed_1229_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14___lam__0___boxed(lean_object* v_fvars_1231_, lean_object* v_f_1232_, lean_object* v_body_1233_, lean_object* v_x_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14___lam__0(v_fvars_1231_, v_f_1232_, v_body_1233_, v_x_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14(lean_object* v_f_1242_, lean_object* v_fvars_1243_, lean_object* v_a_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
if (lean_obj_tag(v_a_1244_) == 7)
{
lean_object* v_binderName_1251_; lean_object* v_binderType_1252_; lean_object* v_body_1253_; uint8_t v_binderInfo_1254_; lean_object* v_d_1255_; lean_object* v___x_1256_; 
v_binderName_1251_ = lean_ctor_get(v_a_1244_, 0);
lean_inc(v_binderName_1251_);
v_binderType_1252_ = lean_ctor_get(v_a_1244_, 1);
lean_inc_ref(v_binderType_1252_);
v_body_1253_ = lean_ctor_get(v_a_1244_, 2);
lean_inc_ref(v_body_1253_);
v_binderInfo_1254_ = lean_ctor_get_uint8(v_a_1244_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_1244_, 3);
v_d_1255_ = lean_expr_instantiate_rev(v_binderType_1252_, v_fvars_1243_);
lean_dec_ref(v_binderType_1252_);
lean_inc_ref(v_f_1242_);
lean_inc(v___y_1249_);
lean_inc_ref(v___y_1248_);
lean_inc(v___y_1247_);
lean_inc_ref(v___y_1246_);
lean_inc(v___y_1245_);
lean_inc_ref(v_d_1255_);
v___x_1256_ = lean_apply_7(v_f_1242_, v_d_1255_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, lean_box(0));
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v___f_1257_; uint8_t v___x_1258_; lean_object* v___x_1259_; 
lean_dec_ref_known(v___x_1256_, 1);
v___f_1257_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1257_, 0, v_fvars_1243_);
lean_closure_set(v___f_1257_, 1, v_f_1242_);
lean_closure_set(v___f_1257_, 2, v_body_1253_);
v___x_1258_ = 0;
v___x_1259_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16___redArg(v_binderName_1251_, v_binderInfo_1254_, v_d_1255_, v___f_1257_, v___x_1258_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
return v___x_1259_;
}
else
{
lean_dec_ref(v_d_1255_);
lean_dec_ref(v_body_1253_);
lean_dec(v_binderName_1251_);
lean_dec_ref(v_fvars_1243_);
lean_dec_ref(v_f_1242_);
return v___x_1256_;
}
}
else
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_expr_instantiate_rev(v_a_1244_, v_fvars_1243_);
lean_dec_ref(v_fvars_1243_);
lean_dec_ref(v_a_1244_);
lean_inc(v___y_1249_);
lean_inc_ref(v___y_1248_);
lean_inc(v___y_1247_);
lean_inc_ref(v___y_1246_);
lean_inc(v___y_1245_);
v___x_1261_ = lean_apply_7(v_f_1242_, v___x_1260_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, lean_box(0));
return v___x_1261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14___lam__0(lean_object* v_fvars_1262_, lean_object* v_f_1263_, lean_object* v_body_1264_, lean_object* v_x_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = lean_array_push(v_fvars_1262_, v_x_1265_);
v___x_1273_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14(v_f_1263_, v___x_1272_, v_body_1264_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14___boxed(lean_object* v_f_1274_, lean_object* v_fvars_1275_, lean_object* v_a_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14(v_f_1274_, v_fvars_1275_, v_a_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(lean_object* v_f_1284_, lean_object* v_e_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_1293_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14(v_f_1284_, v___x_1292_, v_e_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10___boxed(lean_object* v_f_1294_, lean_object* v_e_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(v_f_1294_, v_e_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__16___lam__0___boxed(lean_object* v_fvars_1303_, lean_object* v_f_1304_, lean_object* v_body_1305_, lean_object* v_x_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__16___lam__0(v_fvars_1303_, v_f_1304_, v_body_1305_, v_x_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__16(lean_object* v_f_1314_, lean_object* v_fvars_1315_, lean_object* v_a_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
if (lean_obj_tag(v_a_1316_) == 6)
{
lean_object* v_binderName_1323_; lean_object* v_binderType_1324_; lean_object* v_body_1325_; uint8_t v_binderInfo_1326_; lean_object* v_d_1327_; lean_object* v___x_1328_; 
v_binderName_1323_ = lean_ctor_get(v_a_1316_, 0);
lean_inc(v_binderName_1323_);
v_binderType_1324_ = lean_ctor_get(v_a_1316_, 1);
lean_inc_ref(v_binderType_1324_);
v_body_1325_ = lean_ctor_get(v_a_1316_, 2);
lean_inc_ref(v_body_1325_);
v_binderInfo_1326_ = lean_ctor_get_uint8(v_a_1316_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_1316_, 3);
v_d_1327_ = lean_expr_instantiate_rev(v_binderType_1324_, v_fvars_1315_);
lean_dec_ref(v_binderType_1324_);
lean_inc_ref(v_f_1314_);
lean_inc(v___y_1321_);
lean_inc_ref(v___y_1320_);
lean_inc(v___y_1319_);
lean_inc_ref(v___y_1318_);
lean_inc(v___y_1317_);
lean_inc_ref(v_d_1327_);
v___x_1328_ = lean_apply_7(v_f_1314_, v_d_1327_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, lean_box(0));
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v___f_1329_; uint8_t v___x_1330_; lean_object* v___x_1331_; 
lean_dec_ref_known(v___x_1328_, 1);
v___f_1329_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__16___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1329_, 0, v_fvars_1315_);
lean_closure_set(v___f_1329_, 1, v_f_1314_);
lean_closure_set(v___f_1329_, 2, v_body_1325_);
v___x_1330_ = 0;
v___x_1331_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16___redArg(v_binderName_1323_, v_binderInfo_1326_, v_d_1327_, v___f_1329_, v___x_1330_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
return v___x_1331_;
}
else
{
lean_dec_ref(v_d_1327_);
lean_dec_ref(v_body_1325_);
lean_dec(v_binderName_1323_);
lean_dec_ref(v_fvars_1315_);
lean_dec_ref(v_f_1314_);
return v___x_1328_;
}
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = lean_expr_instantiate_rev(v_a_1316_, v_fvars_1315_);
lean_dec_ref(v_fvars_1315_);
lean_dec_ref(v_a_1316_);
lean_inc(v___y_1321_);
lean_inc_ref(v___y_1320_);
lean_inc(v___y_1319_);
lean_inc_ref(v___y_1318_);
lean_inc(v___y_1317_);
v___x_1333_ = lean_apply_7(v_f_1314_, v___x_1332_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, lean_box(0));
return v___x_1333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__16___lam__0(lean_object* v_fvars_1334_, lean_object* v_f_1335_, lean_object* v_body_1336_, lean_object* v_x_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = lean_array_push(v_fvars_1334_, v_x_1337_);
v___x_1345_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__16(v_f_1335_, v___x_1344_, v_body_1336_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__16___boxed(lean_object* v_f_1346_, lean_object* v_fvars_1347_, lean_object* v_a_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__16(v_f_1346_, v_fvars_1347_, v_a_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(lean_object* v_f_1356_, lean_object* v_e_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_1365_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__16(v_f_1356_, v___x_1364_, v_e_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11___boxed(lean_object* v_f_1366_, lean_object* v_e_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(v_f_1366_, v_e_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18_spec__21___redArg(lean_object* v_name_1375_, lean_object* v_type_1376_, lean_object* v_val_1377_, lean_object* v_k_1378_, uint8_t v_nondep_1379_, uint8_t v_kind_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v___f_1387_; lean_object* v___x_1388_; 
lean_inc(v___y_1381_);
v___f_1387_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1387_, 0, v_k_1378_);
lean_closure_set(v___f_1387_, 1, v___y_1381_);
v___x_1388_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1375_, v_type_1376_, v_val_1377_, v___f_1387_, v_nondep_1379_, v_kind_1380_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
if (lean_obj_tag(v___x_1388_) == 0)
{
return v___x_1388_;
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18_spec__21___redArg___boxed(lean_object* v_name_1397_, lean_object* v_type_1398_, lean_object* v_val_1399_, lean_object* v_k_1400_, lean_object* v_nondep_1401_, lean_object* v_kind_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
uint8_t v_nondep_boxed_1409_; uint8_t v_kind_boxed_1410_; lean_object* v_res_1411_; 
v_nondep_boxed_1409_ = lean_unbox(v_nondep_1401_);
v_kind_boxed_1410_ = lean_unbox(v_kind_1402_);
v_res_1411_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18_spec__21___redArg(v_name_1397_, v_type_1398_, v_val_1399_, v_k_1400_, v_nondep_boxed_1409_, v_kind_boxed_1410_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18___lam__0___boxed(lean_object* v_fvars_1412_, lean_object* v_f_1413_, lean_object* v_body_1414_, lean_object* v_x_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18___lam__0(v_fvars_1412_, v_f_1413_, v_body_1414_, v_x_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18(lean_object* v_f_1423_, lean_object* v_fvars_1424_, lean_object* v_a_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
if (lean_obj_tag(v_a_1425_) == 8)
{
lean_object* v_declName_1432_; lean_object* v_type_1433_; lean_object* v_value_1434_; lean_object* v_body_1435_; lean_object* v_d_1436_; lean_object* v___x_1437_; 
v_declName_1432_ = lean_ctor_get(v_a_1425_, 0);
lean_inc(v_declName_1432_);
v_type_1433_ = lean_ctor_get(v_a_1425_, 1);
lean_inc_ref(v_type_1433_);
v_value_1434_ = lean_ctor_get(v_a_1425_, 2);
lean_inc_ref(v_value_1434_);
v_body_1435_ = lean_ctor_get(v_a_1425_, 3);
lean_inc_ref(v_body_1435_);
lean_dec_ref_known(v_a_1425_, 4);
v_d_1436_ = lean_expr_instantiate_rev(v_type_1433_, v_fvars_1424_);
lean_dec_ref(v_type_1433_);
lean_inc_ref(v_f_1423_);
lean_inc(v___y_1430_);
lean_inc_ref(v___y_1429_);
lean_inc(v___y_1428_);
lean_inc_ref(v___y_1427_);
lean_inc(v___y_1426_);
lean_inc_ref(v_d_1436_);
v___x_1437_ = lean_apply_7(v_f_1423_, v_d_1436_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, lean_box(0));
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_v_1438_; lean_object* v___x_1439_; 
lean_dec_ref_known(v___x_1437_, 1);
v_v_1438_ = lean_expr_instantiate_rev(v_value_1434_, v_fvars_1424_);
lean_dec_ref(v_value_1434_);
lean_inc_ref(v_f_1423_);
lean_inc(v___y_1430_);
lean_inc_ref(v___y_1429_);
lean_inc(v___y_1428_);
lean_inc_ref(v___y_1427_);
lean_inc(v___y_1426_);
lean_inc_ref(v_v_1438_);
v___x_1439_ = lean_apply_7(v_f_1423_, v_v_1438_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, lean_box(0));
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v___f_1440_; uint8_t v___x_1441_; uint8_t v___x_1442_; lean_object* v___x_1443_; 
lean_dec_ref_known(v___x_1439_, 1);
v___f_1440_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1440_, 0, v_fvars_1424_);
lean_closure_set(v___f_1440_, 1, v_f_1423_);
lean_closure_set(v___f_1440_, 2, v_body_1435_);
v___x_1441_ = 0;
v___x_1442_ = 0;
v___x_1443_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18_spec__21___redArg(v_declName_1432_, v_d_1436_, v_v_1438_, v___f_1440_, v___x_1441_, v___x_1442_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
return v___x_1443_;
}
else
{
lean_dec_ref(v_v_1438_);
lean_dec_ref(v_d_1436_);
lean_dec_ref(v_body_1435_);
lean_dec(v_declName_1432_);
lean_dec_ref(v_fvars_1424_);
lean_dec_ref(v_f_1423_);
return v___x_1439_;
}
}
else
{
lean_dec_ref(v_d_1436_);
lean_dec_ref(v_body_1435_);
lean_dec_ref(v_value_1434_);
lean_dec(v_declName_1432_);
lean_dec_ref(v_fvars_1424_);
lean_dec_ref(v_f_1423_);
return v___x_1437_;
}
}
else
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = lean_expr_instantiate_rev(v_a_1425_, v_fvars_1424_);
lean_dec_ref(v_fvars_1424_);
lean_dec_ref(v_a_1425_);
lean_inc(v___y_1430_);
lean_inc_ref(v___y_1429_);
lean_inc(v___y_1428_);
lean_inc_ref(v___y_1427_);
lean_inc(v___y_1426_);
v___x_1445_ = lean_apply_7(v_f_1423_, v___x_1444_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, lean_box(0));
return v___x_1445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18___lam__0(lean_object* v_fvars_1446_, lean_object* v_f_1447_, lean_object* v_body_1448_, lean_object* v_x_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_array_push(v_fvars_1446_, v_x_1449_);
v___x_1457_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18(v_f_1447_, v___x_1456_, v_body_1448_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18___boxed(lean_object* v_f_1458_, lean_object* v_fvars_1459_, lean_object* v_a_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18(v_f_1458_, v_fvars_1459_, v_a_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12(lean_object* v_f_1468_, lean_object* v_e_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_1477_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18(v_f_1468_, v___x_1476_, v_e_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12___boxed(lean_object* v_f_1478_, lean_object* v_e_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12(v_f_1478_, v_e_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed(lean_object* v_fn_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2(v_fn_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(lean_object* v_fn_1496_, lean_object* v_e_1497_, lean_object* v_a_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_a_1505_; lean_object* v___y_1517_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_inc(v_a_1498_);
v___x_1519_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1519_, 0, lean_box(0));
lean_closure_set(v___x_1519_, 1, lean_box(0));
lean_closure_set(v___x_1519_, 2, v_a_1498_);
v___x_1520_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_box(0), v___x_1519_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1557_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1523_ = v___x_1520_;
v_isShared_1524_ = v_isSharedCheck_1557_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1520_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1557_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_a_1521_, v_e_1497_);
lean_dec(v_a_1521_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v___x_1526_; 
lean_del_object(v___x_1523_);
lean_inc_ref(v_fn_1496_);
lean_inc(v___y_1502_);
lean_inc_ref(v___y_1501_);
lean_inc(v___y_1500_);
lean_inc_ref(v___y_1499_);
lean_inc_ref(v_e_1497_);
v___x_1526_ = lean_apply_6(v_fn_1496_, v_e_1497_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, lean_box(0));
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; uint8_t v___x_1528_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
v___x_1528_ = lean_unbox(v_a_1527_);
lean_dec(v_a_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
lean_dec_ref(v_fn_1496_);
v___x_1529_ = lean_box(0);
v_a_1505_ = v___x_1529_;
goto v___jp_1504_;
}
else
{
switch(lean_obj_tag(v_e_1497_))
{
case 7:
{
lean_object* v___f_1530_; lean_object* v___x_1531_; 
v___f_1530_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1530_, 0, v_fn_1496_);
lean_inc_ref(v_e_1497_);
v___x_1531_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(v___f_1530_, v_e_1497_, v_a_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
v___y_1517_ = v___x_1531_;
goto v___jp_1516_;
}
case 6:
{
lean_object* v___f_1532_; lean_object* v___x_1533_; 
v___f_1532_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1532_, 0, v_fn_1496_);
lean_inc_ref(v_e_1497_);
v___x_1533_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(v___f_1532_, v_e_1497_, v_a_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
v___y_1517_ = v___x_1533_;
goto v___jp_1516_;
}
case 8:
{
lean_object* v___f_1534_; lean_object* v___x_1535_; 
v___f_1534_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1534_, 0, v_fn_1496_);
lean_inc_ref(v_e_1497_);
v___x_1535_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12(v___f_1534_, v_e_1497_, v_a_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
v___y_1517_ = v___x_1535_;
goto v___jp_1516_;
}
case 5:
{
lean_object* v_fn_1536_; lean_object* v_arg_1537_; lean_object* v___x_1538_; 
v_fn_1536_ = lean_ctor_get(v_e_1497_, 0);
v_arg_1537_ = lean_ctor_get(v_e_1497_, 1);
lean_inc_ref(v_fn_1536_);
lean_inc_ref(v_fn_1496_);
v___x_1538_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1496_, v_fn_1536_, v_a_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v___x_1539_; 
lean_dec_ref_known(v___x_1538_, 1);
lean_inc_ref(v_arg_1537_);
v___x_1539_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1496_, v_arg_1537_, v_a_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
v___y_1517_ = v___x_1539_;
goto v___jp_1516_;
}
else
{
lean_dec_ref(v_fn_1496_);
v___y_1517_ = v___x_1538_;
goto v___jp_1516_;
}
}
case 10:
{
lean_object* v_expr_1540_; lean_object* v___x_1541_; 
v_expr_1540_ = lean_ctor_get(v_e_1497_, 1);
lean_inc_ref(v_expr_1540_);
v___x_1541_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1496_, v_expr_1540_, v_a_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
v___y_1517_ = v___x_1541_;
goto v___jp_1516_;
}
case 11:
{
lean_object* v_struct_1542_; lean_object* v___x_1543_; 
v_struct_1542_ = lean_ctor_get(v_e_1497_, 2);
lean_inc_ref(v_struct_1542_);
v___x_1543_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1496_, v_struct_1542_, v_a_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
v___y_1517_ = v___x_1543_;
goto v___jp_1516_;
}
default: 
{
lean_object* v___x_1544_; 
lean_dec_ref(v_fn_1496_);
v___x_1544_ = lean_box(0);
v_a_1505_ = v___x_1544_;
goto v___jp_1504_;
}
}
}
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec_ref(v_e_1497_);
lean_dec_ref(v_fn_1496_);
v_a_1545_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1526_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1526_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
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
else
{
lean_object* v_val_1553_; lean_object* v___x_1555_; 
lean_dec_ref(v_e_1497_);
lean_dec_ref(v_fn_1496_);
v_val_1553_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_val_1553_);
lean_dec_ref_known(v___x_1525_, 1);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v_val_1553_);
v___x_1555_ = v___x_1523_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_val_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec_ref(v_e_1497_);
lean_dec_ref(v_fn_1496_);
v_a_1558_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1520_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1520_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
v___jp_1504_:
{
lean_object* v___f_1506_; lean_object* v___x_1507_; 
lean_inc(v_a_1498_);
v___f_1506_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1506_, 0, v_a_1498_);
lean_closure_set(v___f_1506_, 1, v_e_1497_);
lean_closure_set(v___f_1506_, 2, v_a_1505_);
v___x_1507_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_box(0), v___f_1506_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; 
v_unused_1515_ = lean_ctor_get(v___x_1507_, 0);
lean_dec(v_unused_1515_);
v___x_1509_ = v___x_1507_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_dec(v___x_1507_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v_a_1505_);
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1505_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
else
{
return v___x_1507_;
}
}
v___jp_1516_:
{
if (lean_obj_tag(v___y_1517_) == 0)
{
lean_object* v_a_1518_; 
v_a_1518_ = lean_ctor_get(v___y_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___y_1517_, 1);
v_a_1505_ = v_a_1518_;
goto v___jp_1504_;
}
else
{
lean_dec_ref(v_e_1497_);
return v___y_1517_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2(lean_object* v_fn_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___boxed(lean_object* v_fn_1575_, lean_object* v_e_1576_, lean_object* v_a_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1575_, v_e_1576_, v_a_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v_a_1577_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_object* v_00_u03b1_1584_, lean_object* v_x_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1591_ = lean_apply_1(v_x_1585_, lean_box(0));
v___x_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0___boxed(lean_object* v_00_u03b1_1593_, lean_object* v_x_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(v_00_u03b1_1593_, v_x_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(lean_object* v_input_1601_, lean_object* v_fn_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v_a_1610_; lean_object* v___x_1611_; 
v___x_1608_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___redArg___closed__3, &l_Lean_Meta_forEachExpr_x27___redArg___closed__3_once, _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__3);
v___x_1609_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_box(0), v___x_1608_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref(v___x_1609_);
v___x_1611_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1602_, v_input_1601_, v_a_1610_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1611_, 1);
v___x_1613_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1613_, 0, lean_box(0));
lean_closure_set(v___x_1613_, 1, lean_box(0));
lean_closure_set(v___x_1613_, 2, v_a_1610_);
v___x_1614_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_box(0), v___x_1613_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1621_ == 0)
{
lean_object* v_unused_1622_; 
v_unused_1622_ = lean_ctor_get(v___x_1614_, 0);
lean_dec(v_unused_1622_);
v___x_1616_ = v___x_1614_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_dec(v___x_1614_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v_a_1612_);
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1612_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
else
{
lean_dec(v_a_1610_);
return v___x_1611_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___boxed(lean_object* v_input_1623_, lean_object* v_fn_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(v_input_1623_, v_fn_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0(lean_object* v_f_1631_, lean_object* v_e_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; 
lean_inc(v___y_1636_);
lean_inc_ref(v___y_1635_);
lean_inc(v___y_1634_);
lean_inc_ref(v___y_1633_);
v___x_1638_ = lean_apply_6(v_f_1631_, v_e_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, lean_box(0));
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1647_; 
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; 
v_unused_1648_ = lean_ctor_get(v___x_1638_, 0);
lean_dec(v_unused_1648_);
v___x_1640_ = v___x_1638_;
v_isShared_1641_ = v_isSharedCheck_1647_;
goto v_resetjp_1639_;
}
else
{
lean_dec(v___x_1638_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1647_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
uint8_t v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1642_ = 1;
v___x_1643_ = lean_box(v___x_1642_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1643_);
v___x_1645_ = v___x_1640_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
v_a_1649_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1638_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1638_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0___boxed(lean_object* v_f_1657_, lean_object* v_e_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0(v_f_1657_, v_e_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(lean_object* v_e_1665_, lean_object* v_f_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___f_1672_; lean_object* v___x_1673_; 
v___f_1672_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1672_, 0, v_f_1666_);
v___x_1673_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(v_e_1665_, v___f_1672_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___boxed(lean_object* v_e_1674_, lean_object* v_f_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(v_e_1674_, v_f_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt(lean_object* v_e_1684_, lean_object* v_isTarget_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v_a_1695_; lean_object* v___f_1696_; lean_object* v___x_1697_; 
v___x_1691_ = lean_unsigned_to_nat(0u);
v___x_1692_ = ((lean_object*)(l_Lean_Meta_setMVarUserNamesAt___closed__0));
v___x_1693_ = lean_st_mk_ref(v___x_1692_);
v___x_1694_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(v_e_1684_, v_a_1687_);
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref(v___x_1694_);
lean_inc(v___x_1693_);
v___f_1696_ = lean_alloc_closure((void*)(l_Lean_Meta_setMVarUserNamesAt___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1696_, 0, v___x_1693_);
lean_closure_set(v___f_1696_, 1, v_isTarget_1685_);
lean_closure_set(v___f_1696_, 2, v___x_1691_);
v___x_1697_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(v_a_1695_, v___f_1696_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1705_; 
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1705_ == 0)
{
lean_object* v_unused_1706_; 
v_unused_1706_ = lean_ctor_get(v___x_1697_, 0);
lean_dec(v_unused_1706_);
v___x_1699_ = v___x_1697_;
v_isShared_1700_ = v_isSharedCheck_1705_;
goto v_resetjp_1698_;
}
else
{
lean_dec(v___x_1697_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1705_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1701_; lean_object* v___x_1703_; 
v___x_1701_ = lean_st_ref_get(v___x_1693_);
lean_dec(v___x_1693_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 0, v___x_1701_);
v___x_1703_ = v___x_1699_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec(v___x_1693_);
v_a_1707_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1697_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1697_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___boxed(lean_object* v_e_1715_, lean_object* v_isTarget_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_Meta_setMVarUserNamesAt(v_e_1715_, v_isTarget_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_);
lean_dec(v_a_1720_);
lean_dec_ref(v_a_1719_);
lean_dec(v_a_1718_);
lean_dec_ref(v_a_1717_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2(lean_object* v_upperBound_1723_, lean_object* v___x_1724_, lean_object* v_val_1725_, lean_object* v_e_1726_, lean_object* v_isTarget_1727_, lean_object* v_inst_1728_, lean_object* v_R_1729_, lean_object* v_a_1730_, lean_object* v_b_1731_, lean_object* v_c_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(v_upperBound_1723_, v___x_1724_, v_val_1725_, v_e_1726_, v_isTarget_1727_, v_a_1730_, v_b_1731_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___boxed(lean_object* v_upperBound_1739_, lean_object* v___x_1740_, lean_object* v_val_1741_, lean_object* v_e_1742_, lean_object* v_isTarget_1743_, lean_object* v_inst_1744_, lean_object* v_R_1745_, lean_object* v_a_1746_, lean_object* v_b_1747_, lean_object* v_c_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2(v_upperBound_1739_, v___x_1740_, v_val_1741_, v_e_1742_, v_isTarget_1743_, v_inst_1744_, v_R_1745_, v_a_1746_, v_b_1747_, v_c_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec_ref(v_isTarget_1743_);
lean_dec_ref(v_e_1742_);
lean_dec_ref(v___x_1740_);
lean_dec(v_upperBound_1739_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_1755_, lean_object* v_m_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_m_1756_, v_a_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___boxed(lean_object* v_00_u03b2_1759_, lean_object* v_m_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7(v_00_u03b2_1759_, v_m_1760_, v_a_1761_);
lean_dec_ref(v_a_1761_);
lean_dec_ref(v_m_1760_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_1763_, lean_object* v_m_1764_, lean_object* v_query_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(v_m_1764_, v_query_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1767_, lean_object* v_m_1768_, lean_object* v_query_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8(v_00_u03b2_1767_, v_m_1768_, v_query_1769_);
lean_dec_ref(v_query_1769_);
lean_dec_ref(v_m_1768_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(lean_object* v_00_u03b2_1771_, lean_object* v_m_1772_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9___redArg(v_m_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9___boxed(lean_object* v_00_u03b2_1774_, lean_object* v_m_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(v_00_u03b2_1774_, v_m_1775_);
lean_dec_ref(v_m_1775_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_1777_, lean_object* v_m_1778_, lean_object* v_query_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(v_m_1778_, v_query_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03b2_1781_, lean_object* v_m_1782_, lean_object* v_query_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8(v_00_u03b2_1781_, v_m_1782_, v_query_1783_);
lean_dec_ref(v_query_1783_);
lean_dec_ref(v_m_1782_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_1785_, lean_object* v_m_1786_, lean_object* v_query_1787_, lean_object* v_x_1788_, lean_object* v_x_1789_, lean_object* v_x_1790_, lean_object* v_x_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_m_1786_, v_query_1787_, v_x_1788_, v_x_1789_, v_x_1790_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b2_1793_, lean_object* v_m_1794_, lean_object* v_query_1795_, lean_object* v_x_1796_, lean_object* v_x_1797_, lean_object* v_x_1798_, lean_object* v_x_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10(v_00_u03b2_1793_, v_m_1794_, v_query_1795_, v_x_1796_, v_x_1797_, v_x_1798_, v_x_1799_);
lean_dec_ref(v_query_1795_);
lean_dec_ref(v_m_1794_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12(lean_object* v_00_u03b2_1801_, lean_object* v_init_1802_, lean_object* v_b_1803_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12___redArg(v_init_1802_, v_b_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12___boxed(lean_object* v_00_u03b2_1805_, lean_object* v_init_1806_, lean_object* v_b_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12(v_00_u03b2_1805_, v_init_1806_, v_b_1807_);
lean_dec_ref(v_b_1807_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16(lean_object* v_00_u03b1_1809_, lean_object* v_name_1810_, uint8_t v_bi_1811_, lean_object* v_type_1812_, lean_object* v_k_1813_, uint8_t v_kind_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16___redArg(v_name_1810_, v_bi_1811_, v_type_1812_, v_k_1813_, v_kind_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1822_, lean_object* v_name_1823_, lean_object* v_bi_1824_, lean_object* v_type_1825_, lean_object* v_k_1826_, lean_object* v_kind_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
uint8_t v_bi_boxed_1834_; uint8_t v_kind_boxed_1835_; lean_object* v_res_1836_; 
v_bi_boxed_1834_ = lean_unbox(v_bi_1824_);
v_kind_boxed_1835_ = lean_unbox(v_kind_1827_);
v_res_1836_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__14_spec__16(v_00_u03b1_1822_, v_name_1823_, v_bi_boxed_1834_, v_type_1825_, v_k_1826_, v_kind_boxed_1835_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18_spec__21(lean_object* v_00_u03b1_1837_, lean_object* v_name_1838_, lean_object* v_type_1839_, lean_object* v_val_1840_, lean_object* v_k_1841_, uint8_t v_nondep_1842_, uint8_t v_kind_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18_spec__21___redArg(v_name_1838_, v_type_1839_, v_val_1840_, v_k_1841_, v_nondep_1842_, v_kind_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18_spec__21___boxed(lean_object* v_00_u03b1_1851_, lean_object* v_name_1852_, lean_object* v_type_1853_, lean_object* v_val_1854_, lean_object* v_k_1855_, lean_object* v_nondep_1856_, lean_object* v_kind_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
uint8_t v_nondep_boxed_1864_; uint8_t v_kind_boxed_1865_; lean_object* v_res_1866_; 
v_nondep_boxed_1864_ = lean_unbox(v_nondep_1856_);
v_kind_boxed_1865_ = lean_unbox(v_kind_1857_);
v_res_1866_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__12_spec__18_spec__21(v_00_u03b1_1851_, v_name_1852_, v_type_1853_, v_val_1854_, v_k_1855_, v_nondep_boxed_1864_, v_kind_boxed_1865_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12_spec__13(lean_object* v_00_u03b2_1867_, lean_object* v_b_1868_, lean_object* v_acc_1869_, lean_object* v_i_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12_spec__13___redArg(v_b_1868_, v_acc_1869_, v_i_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12_spec__13___boxed(lean_object* v_00_u03b2_1872_, lean_object* v_b_1873_, lean_object* v_acc_1874_, lean_object* v_i_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__12_spec__13(v_00_u03b2_1872_, v_b_1873_, v_acc_1874_, v_i_1875_);
lean_dec_ref(v_b_1873_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(lean_object* v_as_1877_, size_t v_sz_1878_, size_t v_i_1879_, lean_object* v_b_1880_, lean_object* v___y_1881_){
_start:
{
uint8_t v___x_1883_; 
v___x_1883_ = lean_usize_dec_lt(v_i_1879_, v_sz_1878_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; 
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v_b_1880_);
return v___x_1884_;
}
else
{
lean_object* v___x_1885_; lean_object* v_mctx_1886_; lean_object* v_cache_1887_; lean_object* v_zetaDeltaFVarIds_1888_; lean_object* v_postponed_1889_; lean_object* v_diag_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1905_; 
v___x_1885_ = lean_st_ref_take(v___y_1881_);
v_mctx_1886_ = lean_ctor_get(v___x_1885_, 0);
v_cache_1887_ = lean_ctor_get(v___x_1885_, 1);
v_zetaDeltaFVarIds_1888_ = lean_ctor_get(v___x_1885_, 2);
v_postponed_1889_ = lean_ctor_get(v___x_1885_, 3);
v_diag_1890_ = lean_ctor_get(v___x_1885_, 4);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1892_ = v___x_1885_;
v_isShared_1893_ = v_isSharedCheck_1905_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_diag_1890_);
lean_inc(v_postponed_1889_);
lean_inc(v_zetaDeltaFVarIds_1888_);
lean_inc(v_cache_1887_);
lean_inc(v_mctx_1886_);
lean_dec(v___x_1885_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1905_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v_a_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1898_; 
v_a_1894_ = lean_array_uget_borrowed(v_as_1877_, v_i_1879_);
v___x_1895_ = lean_box(0);
lean_inc(v_a_1894_);
v___x_1896_ = l_Lean_MetavarContext_setMVarUserNameTemporarily(v_mctx_1886_, v_a_1894_, v___x_1895_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v___x_1896_);
v___x_1898_ = v___x_1892_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_cache_1887_);
lean_ctor_set(v_reuseFailAlloc_1904_, 2, v_zetaDeltaFVarIds_1888_);
lean_ctor_set(v_reuseFailAlloc_1904_, 3, v_postponed_1889_);
lean_ctor_set(v_reuseFailAlloc_1904_, 4, v_diag_1890_);
v___x_1898_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; size_t v___x_1901_; size_t v___x_1902_; 
v___x_1899_ = lean_st_ref_put(v___y_1881_, v___x_1898_);
v___x_1900_ = lean_box(0);
v___x_1901_ = ((size_t)1ULL);
v___x_1902_ = lean_usize_add(v_i_1879_, v___x_1901_);
v_i_1879_ = v___x_1902_;
v_b_1880_ = v___x_1900_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg___boxed(lean_object* v_as_1906_, lean_object* v_sz_1907_, lean_object* v_i_1908_, lean_object* v_b_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
size_t v_sz_boxed_1912_; size_t v_i_boxed_1913_; lean_object* v_res_1914_; 
v_sz_boxed_1912_ = lean_unbox_usize(v_sz_1907_);
lean_dec(v_sz_1907_);
v_i_boxed_1913_ = lean_unbox_usize(v_i_1908_);
lean_dec(v_i_1908_);
v_res_1914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_as_1906_, v_sz_boxed_1912_, v_i_boxed_1913_, v_b_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v_as_1906_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_resetMVarUserNames(lean_object* v_toReset_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_){
_start:
{
lean_object* v___x_1921_; size_t v_sz_1922_; size_t v___x_1923_; lean_object* v___x_1924_; 
v___x_1921_ = lean_box(0);
v_sz_1922_ = lean_array_size(v_toReset_1915_);
v___x_1923_ = ((size_t)0ULL);
v___x_1924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_toReset_1915_, v_sz_1922_, v___x_1923_, v___x_1921_, v_a_1917_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1931_ == 0)
{
lean_object* v_unused_1932_; 
v_unused_1932_ = lean_ctor_get(v___x_1924_, 0);
lean_dec(v_unused_1932_);
v___x_1926_ = v___x_1924_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_dec(v___x_1924_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1921_);
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1921_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
else
{
return v___x_1924_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_resetMVarUserNames___boxed(lean_object* v_toReset_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Lean_Meta_resetMVarUserNames(v_toReset_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_);
lean_dec(v_a_1937_);
lean_dec_ref(v_a_1936_);
lean_dec(v_a_1935_);
lean_dec_ref(v_a_1934_);
lean_dec_ref(v_toReset_1933_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0(lean_object* v_as_1940_, size_t v_sz_1941_, size_t v_i_1942_, lean_object* v_b_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_as_1940_, v_sz_1941_, v_i_1942_, v_b_1943_, v___y_1945_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___boxed(lean_object* v_as_1950_, lean_object* v_sz_1951_, lean_object* v_i_1952_, lean_object* v_b_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
size_t v_sz_boxed_1959_; size_t v_i_boxed_1960_; lean_object* v_res_1961_; 
v_sz_boxed_1959_ = lean_unbox_usize(v_sz_1951_);
lean_dec(v_sz_1951_);
v_i_boxed_1960_ = lean_unbox_usize(v_i_1952_);
lean_dec(v_i_1952_);
v_res_1961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0(v_as_1950_, v_sz_boxed_1959_, v_i_boxed_1960_, v_b_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec_ref(v_as_1950_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(lean_object* v_x_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
if (lean_obj_tag(v_x_1962_) == 2)
{
lean_object* v_mvarId_1968_; lean_object* v___x_1969_; 
v_mvarId_1968_ = lean_ctor_get(v_x_1962_, 0);
lean_inc(v_mvarId_1968_);
lean_dec_ref_known(v_x_1962_, 1);
v___x_1969_ = l_Lean_MVarId_getDecl(v_mvarId_1968_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1980_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_1980_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1980_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_userName_1974_; uint8_t v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1978_; 
v_userName_1974_ = lean_ctor_get(v_a_1970_, 0);
lean_inc(v_userName_1974_);
lean_dec(v_a_1970_);
v___x_1975_ = l_Lean_Name_isAnonymous(v_userName_1974_);
lean_dec(v_userName_1974_);
v___x_1976_ = lean_box(v___x_1975_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1976_);
v___x_1978_ = v___x_1972_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
v_a_1981_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1969_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1969_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
else
{
uint8_t v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_dec_ref(v_x_1962_);
v___x_1989_ = 0;
v___x_1990_ = lean_box(v___x_1989_);
v___x_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
return v___x_1991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0___boxed(lean_object* v_x_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(v_x_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__0(lean_object* v_val_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_x3f_2004_){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_st_ref_get(v_val_1999_);
v___x_2007_ = l_Lean_Meta_resetMVarUserNames(v___x_2006_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_);
lean_dec(v___x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__0___boxed(lean_object* v_val_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_x3f_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lean_Meta_mkForallFVars_x27___lam__0(v_val_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_x3f_2013_);
lean_dec(v_a_x3f_2013_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec(v_val_2008_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(lean_object* v_xs_2016_, lean_object* v_as_2017_, size_t v_sz_2018_, size_t v_i_2019_, lean_object* v_b_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
uint8_t v___x_2027_; 
v___x_2027_ = lean_usize_dec_lt(v_i_2019_, v_sz_2018_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; 
lean_dec_ref(v_xs_2016_);
v___x_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2028_, 0, v_b_2020_);
return v___x_2028_;
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2030_; 
v_a_2029_ = lean_array_uget_borrowed(v_as_2017_, v_i_2019_);
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
lean_inc(v___y_2023_);
lean_inc_ref(v___y_2022_);
lean_inc(v_a_2029_);
v___x_2030_ = lean_infer_type(v_a_2029_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2032_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___x_2030_, 1);
lean_inc_ref(v_xs_2016_);
v___x_2032_ = l_Lean_Meta_setMVarUserNamesAt(v_a_2031_, v_xs_2016_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; size_t v___x_2038_; size_t v___x_2039_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___x_2032_, 1);
v___x_2034_ = lean_st_ref_take(v___y_2021_);
v___x_2035_ = l_Array_append___redArg(v___x_2034_, v_a_2033_);
lean_dec(v_a_2033_);
v___x_2036_ = lean_st_ref_put(v___y_2021_, v___x_2035_);
v___x_2037_ = lean_box(0);
v___x_2038_ = ((size_t)1ULL);
v___x_2039_ = lean_usize_add(v_i_2019_, v___x_2038_);
v_i_2019_ = v___x_2039_;
v_b_2020_ = v___x_2037_;
goto _start;
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec_ref(v_xs_2016_);
v_a_2041_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2032_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2032_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec_ref(v_xs_2016_);
v_a_2049_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2030_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2030_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2___boxed(lean_object* v_xs_2057_, lean_object* v_as_2058_, lean_object* v_sz_2059_, lean_object* v_i_2060_, lean_object* v_b_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
size_t v_sz_boxed_2068_; size_t v_i_boxed_2069_; lean_object* v_res_2070_; 
v_sz_boxed_2068_ = lean_unbox_usize(v_sz_2059_);
lean_dec(v_sz_2059_);
v_i_boxed_2069_ = lean_unbox_usize(v_i_2060_);
lean_dec(v_i_2060_);
v_res_2070_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(v_xs_2057_, v_as_2058_, v_sz_boxed_2068_, v_i_boxed_2069_, v_b_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v_as_2058_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(lean_object* v_xs_2071_, lean_object* v_as_2072_, size_t v_sz_2073_, size_t v_i_2074_, lean_object* v_b_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
uint8_t v___x_2082_; 
v___x_2082_ = lean_usize_dec_lt(v_i_2074_, v_sz_2073_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; 
lean_dec_ref(v_xs_2071_);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v_b_2075_);
return v___x_2083_;
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2085_; 
v_a_2084_ = lean_array_uget_borrowed(v_as_2072_, v_i_2074_);
lean_inc(v___y_2080_);
lean_inc_ref(v___y_2079_);
lean_inc(v___y_2078_);
lean_inc_ref(v___y_2077_);
lean_inc(v_a_2084_);
v___x_2085_ = lean_infer_type(v_a_2084_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2087_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2085_, 1);
lean_inc_ref(v_xs_2071_);
v___x_2087_ = l_Lean_Meta_setMVarUserNamesAt(v_a_2086_, v_xs_2071_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; size_t v___x_2093_; size_t v___x_2094_; lean_object* v___x_2095_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2087_, 1);
v___x_2089_ = lean_st_ref_take(v___y_2076_);
v___x_2090_ = l_Array_append___redArg(v___x_2089_, v_a_2088_);
lean_dec(v_a_2088_);
v___x_2091_ = lean_st_ref_put(v___y_2076_, v___x_2090_);
v___x_2092_ = lean_box(0);
v___x_2093_ = ((size_t)1ULL);
v___x_2094_ = lean_usize_add(v_i_2074_, v___x_2093_);
v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(v_xs_2071_, v_as_2072_, v_sz_2073_, v___x_2094_, v___x_2092_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
return v___x_2095_;
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec_ref(v_xs_2071_);
v_a_2096_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2087_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2087_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec_ref(v_xs_2071_);
v_a_2104_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2085_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2085_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2___boxed(lean_object* v_xs_2112_, lean_object* v_as_2113_, lean_object* v_sz_2114_, lean_object* v_i_2115_, lean_object* v_b_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
size_t v_sz_boxed_2123_; size_t v_i_boxed_2124_; lean_object* v_res_2125_; 
v_sz_boxed_2123_ = lean_unbox_usize(v_sz_2114_);
lean_dec(v_sz_2114_);
v_i_boxed_2124_ = lean_unbox_usize(v_i_2115_);
lean_dec(v_i_2115_);
v_res_2125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(v_xs_2112_, v_as_2113_, v_sz_boxed_2123_, v_i_boxed_2124_, v_b_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec_ref(v_as_2113_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(lean_object* v_as_2126_, size_t v_i_2127_, size_t v_stop_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
uint8_t v___x_2134_; 
v___x_2134_ = lean_usize_dec_eq(v_i_2127_, v_stop_2128_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_array_uget_borrowed(v_as_2126_, v_i_2127_);
lean_inc(v___x_2135_);
v___x_2136_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(v___x_2135_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2148_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2139_ = v___x_2136_;
v_isShared_2140_ = v_isSharedCheck_2148_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2136_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2148_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
uint8_t v___x_2141_; 
v___x_2141_ = lean_unbox(v_a_2137_);
if (v___x_2141_ == 0)
{
size_t v___x_2142_; size_t v___x_2143_; 
lean_del_object(v___x_2139_);
lean_dec(v_a_2137_);
v___x_2142_ = ((size_t)1ULL);
v___x_2143_ = lean_usize_add(v_i_2127_, v___x_2142_);
v_i_2127_ = v___x_2143_;
goto _start;
}
else
{
lean_object* v___x_2146_; 
if (v_isShared_2140_ == 0)
{
v___x_2146_ = v___x_2139_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2137_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
else
{
return v___x_2136_;
}
}
else
{
uint8_t v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2149_ = 0;
v___x_2150_ = lean_box(v___x_2149_);
v___x_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
return v___x_2151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1___boxed(lean_object* v_as_2152_, lean_object* v_i_2153_, lean_object* v_stop_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
size_t v_i_boxed_2160_; size_t v_stop_boxed_2161_; lean_object* v_res_2162_; 
v_i_boxed_2160_ = lean_unbox_usize(v_i_2153_);
lean_dec(v_i_2153_);
v_stop_boxed_2161_ = lean_unbox_usize(v_stop_2154_);
lean_dec(v_stop_2154_);
v_res_2162_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(v_as_2152_, v_i_boxed_2160_, v_stop_boxed_2161_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec_ref(v_as_2152_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27(lean_object* v_xs_2163_, lean_object* v_type_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
uint8_t v_a_2171_; lean_object* v___x_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2175_ = lean_unsigned_to_nat(0u);
v___x_2176_ = lean_array_get_size(v_xs_2163_);
v___x_2177_ = lean_nat_dec_lt(v___x_2175_, v___x_2176_);
if (v___x_2177_ == 0)
{
v_a_2171_ = v___x_2177_;
goto v___jp_2170_;
}
else
{
if (v___x_2177_ == 0)
{
v_a_2171_ = v___x_2177_;
goto v___jp_2170_;
}
else
{
size_t v___x_2178_; size_t v___x_2179_; lean_object* v___x_2180_; 
v___x_2178_ = ((size_t)0ULL);
v___x_2179_ = lean_usize_of_nat(v___x_2176_);
v___x_2180_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(v_xs_2163_, v___x_2178_, v___x_2179_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; uint8_t v___x_2182_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2180_, 1);
v___x_2182_ = lean_unbox(v_a_2181_);
if (v___x_2182_ == 0)
{
uint8_t v___x_2183_; 
v___x_2183_ = lean_unbox(v_a_2181_);
lean_dec(v_a_2181_);
v_a_2171_ = v___x_2183_;
goto v___jp_2170_;
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v_a_2187_; lean_object* v___x_2206_; size_t v_sz_2207_; lean_object* v___x_2208_; 
lean_dec(v_a_2181_);
v___x_2184_ = ((lean_object*)(l_Lean_Meta_setMVarUserNamesAt___closed__0));
v___x_2185_ = lean_st_mk_ref(v___x_2184_);
v___x_2206_ = lean_box(0);
v_sz_2207_ = lean_array_size(v_xs_2163_);
lean_inc_ref(v_xs_2163_);
v___x_2208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(v_xs_2163_, v_xs_2163_, v_sz_2207_, v___x_2178_, v___x_2206_, v___x_2185_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v___x_2209_; 
lean_dec_ref_known(v___x_2208_, 1);
lean_inc_ref(v_xs_2163_);
lean_inc_ref(v_type_2164_);
v___x_2209_ = l_Lean_Meta_setMVarUserNamesAt(v_type_2164_, v_xs_2163_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; uint8_t v___x_2215_; lean_object* v___x_2216_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref_known(v___x_2209_, 1);
v___x_2211_ = lean_st_ref_take(v___x_2185_);
v___x_2212_ = l_Array_append___redArg(v___x_2211_, v_a_2210_);
lean_dec(v_a_2210_);
v___x_2213_ = lean_st_ref_put(v___x_2185_, v___x_2212_);
v___x_2214_ = 0;
v___x_2215_ = 1;
v___x_2216_ = l_Lean_Meta_mkForallFVars(v_xs_2163_, v_type_2164_, v___x_2214_, v___x_2177_, v___x_2177_, v___x_2215_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
lean_dec_ref(v_xs_2163_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2242_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2219_ = v___x_2216_;
v_isShared_2220_ = v_isSharedCheck_2242_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2216_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2242_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
lean_inc(v_a_2217_);
if (v_isShared_2220_ == 0)
{
lean_ctor_set_tag(v___x_2219_, 1);
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Lean_Meta_mkForallFVars_x27___lam__0(v___x_2185_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v___x_2222_);
lean_dec_ref(v___x_2222_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2231_; 
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2231_ == 0)
{
lean_object* v_unused_2232_; 
v_unused_2232_ = lean_ctor_get(v___x_2223_, 0);
lean_dec(v_unused_2232_);
v___x_2225_ = v___x_2223_;
v_isShared_2226_ = v_isSharedCheck_2231_;
goto v_resetjp_2224_;
}
else
{
lean_dec(v___x_2223_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2231_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2227_ = lean_st_ref_get(v___x_2185_);
lean_dec(v___x_2185_);
lean_dec(v___x_2227_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v_a_2217_);
v___x_2229_ = v___x_2225_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2217_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec(v_a_2217_);
lean_dec(v___x_2185_);
v_a_2233_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2223_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2223_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
}
}
else
{
lean_object* v_a_2243_; 
v_a_2243_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2243_);
lean_dec_ref_known(v___x_2216_, 1);
v_a_2187_ = v_a_2243_;
goto v___jp_2186_;
}
}
else
{
lean_object* v_a_2244_; 
lean_dec_ref(v_type_2164_);
lean_dec_ref(v_xs_2163_);
v_a_2244_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2244_);
lean_dec_ref_known(v___x_2209_, 1);
v_a_2187_ = v_a_2244_;
goto v___jp_2186_;
}
}
else
{
lean_object* v_a_2245_; 
lean_dec_ref(v_type_2164_);
lean_dec_ref(v_xs_2163_);
v_a_2245_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2245_);
lean_dec_ref_known(v___x_2208_, 1);
v_a_2187_ = v_a_2245_;
goto v___jp_2186_;
}
v___jp_2186_:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = lean_box(0);
v___x_2189_ = l_Lean_Meta_mkForallFVars_x27___lam__0(v___x_2185_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v___x_2188_);
lean_dec(v___x_2185_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2196_ == 0)
{
lean_object* v_unused_2197_; 
v_unused_2197_ = lean_ctor_get(v___x_2189_, 0);
lean_dec(v_unused_2197_);
v___x_2191_ = v___x_2189_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_dec(v___x_2189_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
lean_ctor_set_tag(v___x_2191_, 1);
lean_ctor_set(v___x_2191_, 0, v_a_2187_);
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2187_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec_ref(v_a_2187_);
v_a_2198_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2189_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2189_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec_ref(v_type_2164_);
lean_dec_ref(v_xs_2163_);
v_a_2246_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2180_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2180_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
v___jp_2170_:
{
uint8_t v___x_2172_; uint8_t v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = 1;
v___x_2173_ = 1;
v___x_2174_ = l_Lean_Meta_mkForallFVars(v_xs_2163_, v_type_2164_, v_a_2171_, v___x_2172_, v___x_2172_, v___x_2173_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
lean_dec_ref(v_xs_2163_);
return v___x_2174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___boxed(lean_object* v_xs_2254_, lean_object* v_type_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_Meta_mkForallFVars_x27(v_xs_2254_, v_type_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
lean_dec(v_a_2259_);
lean_dec_ref(v_a_2258_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
return v_res_2261_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_ForEachExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_ForEachExpr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_ForEachExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_ForEachExpr(builtin);
}
#ifdef __cplusplus
}
#endif
