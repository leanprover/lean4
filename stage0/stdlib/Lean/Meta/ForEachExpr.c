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
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Lean_MonadCacheT_instMonad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadCacheT_instMonadControl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_withLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_MetavarContext_setMVarUserNameTemporarily(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_a_23_);
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
lean_dec_ref(v_a_70_);
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
lean_dec_ref(v_a_132_);
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
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = lean_box(0);
v___x_185_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_179_, v___x_180_, v_s_183_, v_e_181_, v_a_182_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_184_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__2(lean_object* v_toApplicative_187_, lean_object* v___x_188_, lean_object* v___x_189_, lean_object* v_e_190_, lean_object* v_a_191_, lean_object* v_x_192_, lean_object* v_toBind_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___f_195_; lean_object* v___f_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___f_195_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__0), 3, 2);
lean_closure_set(v___f_195_, 0, v_toApplicative_187_);
lean_closure_set(v___f_195_, 1, v_a_194_);
v___f_196_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__1), 5, 4);
lean_closure_set(v___f_196_, 0, v___x_188_);
lean_closure_set(v___f_196_, 1, v___x_189_);
lean_closure_set(v___f_196_, 2, v_e_190_);
lean_closure_set(v___f_196_, 3, v_a_194_);
lean_inc(v_a_191_);
v___x_197_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_197_, 0, lean_box(0));
lean_closure_set(v___x_197_, 1, lean_box(0));
lean_closure_set(v___x_197_, 2, lean_box(0));
lean_closure_set(v___x_197_, 3, v_a_191_);
lean_closure_set(v___x_197_, 4, v___f_196_);
v___x_198_ = lean_apply_2(v_x_192_, lean_box(0), v___x_197_);
v___x_199_ = lean_apply_4(v_toBind_193_, lean_box(0), lean_box(0), v___x_198_, v___f_195_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_200_, lean_object* v___x_201_, lean_object* v___x_202_, lean_object* v_e_203_, lean_object* v_a_204_, lean_object* v_x_205_, lean_object* v_toBind_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__2(v_toApplicative_200_, v___x_201_, v___x_202_, v_e_203_, v_a_204_, v_x_205_, v_toBind_206_, v_a_207_);
lean_dec(v_a_204_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__3(lean_object* v_toApplicative_209_, lean_object* v___x_210_, lean_object* v___x_211_, lean_object* v_e_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_toPure_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_toPure_214_ = lean_ctor_get(v_toApplicative_209_, 1);
lean_inc(v_toPure_214_);
lean_dec_ref(v_toApplicative_209_);
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_210_, v___x_211_, v_a_213_, v_e_212_);
v___x_216_ = lean_apply_2(v_toPure_214_, lean_box(0), v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__3___boxed(lean_object* v_toApplicative_217_, lean_object* v___x_218_, lean_object* v___x_219_, lean_object* v_e_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__3(v_toApplicative_217_, v___x_218_, v___x_219_, v_e_220_, v_a_221_);
lean_dec_ref(v_a_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__6(lean_object* v_fn_223_, lean_object* v_e_224_, lean_object* v_toBind_225_, lean_object* v___f_226_, lean_object* v___f_227_, lean_object* v_toApplicative_228_, lean_object* v_a_229_){
_start:
{
if (lean_obj_tag(v_a_229_) == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
lean_dec_ref(v_toApplicative_228_);
v___x_230_ = lean_apply_1(v_fn_223_, v_e_224_);
lean_inc(v_toBind_225_);
v___x_231_ = lean_apply_4(v_toBind_225_, lean_box(0), lean_box(0), v___x_230_, v___f_226_);
v___x_232_ = lean_apply_4(v_toBind_225_, lean_box(0), lean_box(0), v___x_231_, v___f_227_);
return v___x_232_;
}
else
{
lean_object* v_val_233_; lean_object* v_toPure_234_; lean_object* v___x_235_; 
lean_dec(v___f_227_);
lean_dec(v___f_226_);
lean_dec(v_toBind_225_);
lean_dec_ref(v_e_224_);
lean_dec(v_fn_223_);
v_val_233_ = lean_ctor_get(v_a_229_, 0);
lean_inc(v_val_233_);
lean_dec_ref(v_a_229_);
v_toPure_234_ = lean_ctor_get(v_toApplicative_228_, 1);
lean_inc(v_toPure_234_);
lean_dec_ref(v_toApplicative_228_);
v___x_235_ = lean_apply_2(v_toPure_234_, lean_box(0), v_val_233_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed(lean_object* v_inst_238_, lean_object* v_inst_239_, lean_object* v_fn_240_, lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_e_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_238_, v_inst_239_, v_fn_240_, v_x_241_, v_x_242_, v_e_243_, v_a_244_);
lean_dec(v_a_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4___boxed(lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_fn_248_, lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_arg_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4(v_inst_246_, v_inst_247_, v_fn_248_, v_x_249_, v_x_250_, v_arg_251_, v_a_252_, v_a_253_);
lean_dec(v_a_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5(lean_object* v_toApplicative_255_, lean_object* v_e_256_, lean_object* v_x_257_, lean_object* v___x_258_, lean_object* v___x_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_fn_262_, lean_object* v_x_263_, lean_object* v___x_264_, lean_object* v_a_265_, lean_object* v_toBind_266_, uint8_t v_a_267_){
_start:
{
if (v_a_267_ == 0)
{
lean_object* v_toPure_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec(v_toBind_266_);
lean_dec_ref(v___x_264_);
lean_dec(v_x_263_);
lean_dec(v_fn_262_);
lean_dec_ref(v_inst_261_);
lean_dec_ref(v_inst_260_);
lean_dec_ref(v___x_259_);
lean_dec_ref(v___x_258_);
lean_dec_ref(v_e_256_);
v_toPure_268_ = lean_ctor_get(v_toApplicative_255_, 1);
lean_inc(v_toPure_268_);
lean_dec_ref(v_toApplicative_255_);
v___x_269_ = lean_box(0);
v___x_270_ = lean_apply_2(v_toPure_268_, lean_box(0), v___x_269_);
return v___x_270_;
}
else
{
switch(lean_obj_tag(v_e_256_))
{
case 7:
{
lean_object* v___x_271_; lean_object* v___f_272_; lean_object* v___f_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_886__overap_276_; lean_object* v___x_277_; 
lean_dec(v_toBind_266_);
lean_dec_ref(v_toApplicative_255_);
v___x_271_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_257_, v___x_258_, v___x_259_);
lean_inc_ref_n(v_inst_260_, 2);
lean_inc_ref(v___x_271_);
v___f_272_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_272_, 0, v___x_271_);
lean_closure_set(v___f_272_, 1, v_inst_260_);
v___f_273_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_273_, 0, v___x_271_);
lean_closure_set(v___f_273_, 1, v_inst_260_);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v___f_272_);
lean_ctor_set(v___x_274_, 1, v___f_273_);
v___x_275_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed), 7, 5);
lean_closure_set(v___x_275_, 0, v_inst_261_);
lean_closure_set(v___x_275_, 1, v_inst_260_);
lean_closure_set(v___x_275_, 2, v_fn_262_);
lean_closure_set(v___x_275_, 3, v_x_257_);
lean_closure_set(v___x_275_, 4, v_x_263_);
v___x_886__overap_276_ = l_Lean_Meta_visitForall___redArg(v___x_264_, v___x_274_, v___x_275_, v_e_256_);
lean_inc(v_a_265_);
v___x_277_ = lean_apply_1(v___x_886__overap_276_, v_a_265_);
return v___x_277_;
}
case 6:
{
lean_object* v___x_278_; lean_object* v___f_279_; lean_object* v___f_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_896__overap_283_; lean_object* v___x_284_; 
lean_dec(v_toBind_266_);
lean_dec_ref(v_toApplicative_255_);
v___x_278_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_257_, v___x_258_, v___x_259_);
lean_inc_ref_n(v_inst_260_, 2);
lean_inc_ref(v___x_278_);
v___f_279_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_279_, 0, v___x_278_);
lean_closure_set(v___f_279_, 1, v_inst_260_);
v___f_280_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_280_, 0, v___x_278_);
lean_closure_set(v___f_280_, 1, v_inst_260_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v___f_279_);
lean_ctor_set(v___x_281_, 1, v___f_280_);
v___x_282_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed), 7, 5);
lean_closure_set(v___x_282_, 0, v_inst_261_);
lean_closure_set(v___x_282_, 1, v_inst_260_);
lean_closure_set(v___x_282_, 2, v_fn_262_);
lean_closure_set(v___x_282_, 3, v_x_257_);
lean_closure_set(v___x_282_, 4, v_x_263_);
v___x_896__overap_283_ = l_Lean_Meta_visitLambda___redArg(v___x_264_, v___x_281_, v___x_282_, v_e_256_);
lean_inc(v_a_265_);
v___x_284_ = lean_apply_1(v___x_896__overap_283_, v_a_265_);
return v___x_284_;
}
case 8:
{
lean_object* v___x_285_; lean_object* v___f_286_; lean_object* v___f_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_907__overap_290_; lean_object* v___x_291_; 
lean_dec(v_toBind_266_);
lean_dec_ref(v_toApplicative_255_);
v___x_285_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_257_, v___x_258_, v___x_259_);
lean_inc_ref_n(v_inst_260_, 2);
lean_inc_ref(v___x_285_);
v___f_286_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_286_, 0, v___x_285_);
lean_closure_set(v___f_286_, 1, v_inst_260_);
v___f_287_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_287_, 0, v___x_285_);
lean_closure_set(v___f_287_, 1, v_inst_260_);
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___f_286_);
lean_ctor_set(v___x_288_, 1, v___f_287_);
v___x_289_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed), 7, 5);
lean_closure_set(v___x_289_, 0, v_inst_261_);
lean_closure_set(v___x_289_, 1, v_inst_260_);
lean_closure_set(v___x_289_, 2, v_fn_262_);
lean_closure_set(v___x_289_, 3, v_x_257_);
lean_closure_set(v___x_289_, 4, v_x_263_);
v___x_907__overap_290_ = l_Lean_Meta_visitLet___redArg(v___x_264_, v___x_288_, v___x_289_, v_e_256_);
lean_inc(v_a_265_);
v___x_291_ = lean_apply_1(v___x_907__overap_290_, v_a_265_);
return v___x_291_;
}
case 5:
{
lean_object* v_fn_292_; lean_object* v_arg_293_; lean_object* v___f_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_259_);
lean_dec_ref(v___x_258_);
lean_dec_ref(v_toApplicative_255_);
v_fn_292_ = lean_ctor_get(v_e_256_, 0);
lean_inc_ref(v_fn_292_);
v_arg_293_ = lean_ctor_get(v_e_256_, 1);
lean_inc_ref(v_arg_293_);
lean_dec_ref(v_e_256_);
lean_inc(v_a_265_);
lean_inc(v_x_263_);
lean_inc(v_fn_262_);
lean_inc_ref(v_inst_260_);
lean_inc_ref(v_inst_261_);
v___f_294_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_294_, 0, v_inst_261_);
lean_closure_set(v___f_294_, 1, v_inst_260_);
lean_closure_set(v___f_294_, 2, v_fn_262_);
lean_closure_set(v___f_294_, 3, v_x_257_);
lean_closure_set(v___f_294_, 4, v_x_263_);
lean_closure_set(v___f_294_, 5, v_arg_293_);
lean_closure_set(v___f_294_, 6, v_a_265_);
v___x_295_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_261_, v_inst_260_, v_fn_262_, v_x_257_, v_x_263_, v_fn_292_, v_a_265_);
v___x_296_ = lean_apply_4(v_toBind_266_, lean_box(0), lean_box(0), v___x_295_, v___f_294_);
return v___x_296_;
}
case 10:
{
lean_object* v_expr_297_; lean_object* v___x_298_; 
lean_dec(v_toBind_266_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_259_);
lean_dec_ref(v___x_258_);
lean_dec_ref(v_toApplicative_255_);
v_expr_297_ = lean_ctor_get(v_e_256_, 1);
lean_inc_ref(v_expr_297_);
lean_dec_ref(v_e_256_);
v___x_298_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_261_, v_inst_260_, v_fn_262_, v_x_257_, v_x_263_, v_expr_297_, v_a_265_);
return v___x_298_;
}
case 11:
{
lean_object* v_struct_299_; lean_object* v___x_300_; 
lean_dec(v_toBind_266_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_259_);
lean_dec_ref(v___x_258_);
lean_dec_ref(v_toApplicative_255_);
v_struct_299_ = lean_ctor_get(v_e_256_, 2);
lean_inc_ref(v_struct_299_);
lean_dec_ref(v_e_256_);
v___x_300_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_261_, v_inst_260_, v_fn_262_, v_x_257_, v_x_263_, v_struct_299_, v_a_265_);
return v___x_300_;
}
default: 
{
lean_object* v_toPure_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec(v_toBind_266_);
lean_dec_ref(v___x_264_);
lean_dec(v_x_263_);
lean_dec(v_fn_262_);
lean_dec_ref(v_inst_261_);
lean_dec_ref(v_inst_260_);
lean_dec_ref(v___x_259_);
lean_dec_ref(v___x_258_);
lean_dec_ref(v_e_256_);
v_toPure_301_ = lean_ctor_get(v_toApplicative_255_, 1);
lean_inc(v_toPure_301_);
lean_dec_ref(v_toApplicative_255_);
v___x_302_ = lean_box(0);
v___x_303_ = lean_apply_2(v_toPure_301_, lean_box(0), v___x_302_);
return v___x_303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___boxed(lean_object* v_toApplicative_304_, lean_object* v_e_305_, lean_object* v_x_306_, lean_object* v___x_307_, lean_object* v___x_308_, lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_fn_311_, lean_object* v_x_312_, lean_object* v___x_313_, lean_object* v_a_314_, lean_object* v_toBind_315_, lean_object* v_a_316_){
_start:
{
uint8_t v_a_boxed_317_; lean_object* v_res_318_; 
v_a_boxed_317_ = lean_unbox(v_a_316_);
v_res_318_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5(v_toApplicative_304_, v_e_305_, v_x_306_, v___x_307_, v___x_308_, v_inst_309_, v_inst_310_, v_fn_311_, v_x_312_, v___x_313_, v_a_314_, v_toBind_315_, v_a_boxed_317_);
lean_dec(v_a_314_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_fn_321_, lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_e_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v_toApplicative_329_; lean_object* v_toBind_330_; lean_object* v___f_331_; lean_object* v___f_332_; lean_object* v___f_333_; lean_object* v___f_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_326_ = ((lean_object*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__0));
v___x_327_ = ((lean_object*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__1));
lean_inc_ref(v_inst_319_);
v___x_328_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_322_, v___x_326_, v___x_327_, v_inst_319_);
v_toApplicative_329_ = lean_ctor_get(v_inst_319_, 0);
lean_inc_ref_n(v_toApplicative_329_, 4);
v_toBind_330_ = lean_ctor_get(v_inst_319_, 1);
lean_inc_n(v_toBind_330_, 5);
lean_inc_n(v_x_323_, 2);
lean_inc_n(v_a_325_, 3);
lean_inc_ref_n(v_e_324_, 3);
v___f_331_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_331_, 0, v_toApplicative_329_);
lean_closure_set(v___f_331_, 1, v___x_326_);
lean_closure_set(v___f_331_, 2, v___x_327_);
lean_closure_set(v___f_331_, 3, v_e_324_);
lean_closure_set(v___f_331_, 4, v_a_325_);
lean_closure_set(v___f_331_, 5, v_x_323_);
lean_closure_set(v___f_331_, 6, v_toBind_330_);
v___f_332_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_332_, 0, v_toApplicative_329_);
lean_closure_set(v___f_332_, 1, v___x_326_);
lean_closure_set(v___f_332_, 2, v___x_327_);
lean_closure_set(v___f_332_, 3, v_e_324_);
lean_inc(v_fn_321_);
v___f_333_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___boxed), 13, 12);
lean_closure_set(v___f_333_, 0, v_toApplicative_329_);
lean_closure_set(v___f_333_, 1, v_e_324_);
lean_closure_set(v___f_333_, 2, v_x_322_);
lean_closure_set(v___f_333_, 3, v___x_326_);
lean_closure_set(v___f_333_, 4, v___x_327_);
lean_closure_set(v___f_333_, 5, v_inst_320_);
lean_closure_set(v___f_333_, 6, v_inst_319_);
lean_closure_set(v___f_333_, 7, v_fn_321_);
lean_closure_set(v___f_333_, 8, v_x_323_);
lean_closure_set(v___f_333_, 9, v___x_328_);
lean_closure_set(v___f_333_, 10, v_a_325_);
lean_closure_set(v___f_333_, 11, v_toBind_330_);
v___f_334_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__6), 7, 6);
lean_closure_set(v___f_334_, 0, v_fn_321_);
lean_closure_set(v___f_334_, 1, v_e_324_);
lean_closure_set(v___f_334_, 2, v_toBind_330_);
lean_closure_set(v___f_334_, 3, v___f_333_);
lean_closure_set(v___f_334_, 4, v___f_331_);
lean_closure_set(v___f_334_, 5, v_toApplicative_329_);
v___x_335_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_335_, 0, lean_box(0));
lean_closure_set(v___x_335_, 1, lean_box(0));
lean_closure_set(v___x_335_, 2, v_a_325_);
v___x_336_ = lean_apply_2(v_x_323_, lean_box(0), v___x_335_);
v___x_337_ = lean_apply_4(v_toBind_330_, lean_box(0), lean_box(0), v___x_336_, v___f_332_);
v___x_338_ = lean_apply_4(v_toBind_330_, lean_box(0), lean_box(0), v___x_337_, v___f_334_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4(lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_fn_341_, lean_object* v_x_342_, lean_object* v_x_343_, lean_object* v_arg_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_339_, v_inst_340_, v_fn_341_, v_x_342_, v_x_343_, v_arg_344_, v_a_345_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit(lean_object* v_m_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_fn_351_, lean_object* v_x_352_, lean_object* v_x_353_, lean_object* v_e_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_349_, v_inst_350_, v_fn_351_, v_x_352_, v_x_353_, v_e_354_, v_a_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___boxed(lean_object* v_m_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_fn_360_, lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v_e_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit(v_m_357_, v_inst_358_, v_inst_359_, v_fn_360_, v_x_361_, v_x_362_, v_e_363_, v_a_364_);
lean_dec(v_a_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__0(lean_object* v_x_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_apply_1(v_x_366_, lean_box(0));
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__0___boxed(lean_object* v_x_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_Meta_forEachExpr_x27___redArg___lam__0(v_x_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__1(lean_object* v_inst_381_, lean_object* v_00_u03b1_382_, lean_object* v_x_383_){
_start:
{
lean_object* v___f_384_; lean_object* v___x_385_; 
v___f_384_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_384_, 0, v_x_383_);
v___x_385_ = lean_apply_2(v_inst_381_, lean_box(0), v___f_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__2(lean_object* v_toPure_386_, lean_object* v_____x_387_){
_start:
{
lean_object* v_fst_388_; lean_object* v___x_389_; 
v_fst_388_ = lean_ctor_get(v_____x_387_, 0);
lean_inc(v_fst_388_);
lean_dec_ref(v_____x_387_);
v___x_389_ = lean_apply_2(v_toPure_386_, lean_box(0), v_fst_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__3(lean_object* v_a_390_, lean_object* v_toPure_391_, lean_object* v_s_392_){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v_a_390_);
lean_ctor_set(v___x_393_, 1, v_s_392_);
v___x_394_ = lean_apply_2(v_toPure_391_, lean_box(0), v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__4(lean_object* v_toPure_395_, lean_object* v_ref_396_, lean_object* v_x_397_, lean_object* v_toBind_398_, lean_object* v_a_399_){
_start:
{
lean_object* v___f_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___f_400_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__3), 3, 2);
lean_closure_set(v___f_400_, 0, v_a_399_);
lean_closure_set(v___f_400_, 1, v_toPure_395_);
v___x_401_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_401_, 0, lean_box(0));
lean_closure_set(v___x_401_, 1, lean_box(0));
lean_closure_set(v___x_401_, 2, v_ref_396_);
v___x_402_ = lean_apply_2(v_x_397_, lean_box(0), v___x_401_);
v___x_403_ = lean_apply_4(v_toBind_398_, lean_box(0), lean_box(0), v___x_402_, v___f_400_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__5(lean_object* v_toPure_404_, lean_object* v_x_405_, lean_object* v_toBind_406_, lean_object* v_inst_407_, lean_object* v_inst_408_, lean_object* v_fn_409_, lean_object* v_x_410_, lean_object* v_input_411_, lean_object* v_ref_412_){
_start:
{
lean_object* v___f_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
lean_inc(v_toBind_406_);
lean_inc(v_x_405_);
lean_inc(v_ref_412_);
v___f_413_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__4), 5, 4);
lean_closure_set(v___f_413_, 0, v_toPure_404_);
lean_closure_set(v___f_413_, 1, v_ref_412_);
lean_closure_set(v___f_413_, 2, v_x_405_);
lean_closure_set(v___f_413_, 3, v_toBind_406_);
v___x_414_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_407_, v_inst_408_, v_fn_409_, v_x_410_, v_x_405_, v_input_411_, v_ref_412_);
lean_dec(v_ref_412_);
v___x_415_ = lean_apply_4(v_toBind_406_, lean_box(0), lean_box(0), v___x_414_, v___f_413_);
return v___x_415_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_box(0);
v___x_417_ = lean_unsigned_to_nat(16u);
v___x_418_ = lean_mk_array(v___x_417_, v___x_416_);
return v___x_418_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__1(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___redArg___closed__0, &l_Lean_Meta_forEachExpr_x27___redArg___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__0);
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___x_419_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__2(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___redArg___closed__1, &l_Lean_Meta_forEachExpr_x27___redArg___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__1);
v___x_423_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_423_, 0, lean_box(0));
lean_closure_set(v___x_423_, 1, lean_box(0));
lean_closure_set(v___x_423_, 2, v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg(lean_object* v_inst_424_, lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_input_427_, lean_object* v_fn_428_){
_start:
{
lean_object* v_x_429_; lean_object* v_toApplicative_430_; lean_object* v_toBind_431_; lean_object* v_toPure_432_; lean_object* v_x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___f_436_; lean_object* v___f_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_x_429_ = lean_box(0);
v_toApplicative_430_ = lean_ctor_get(v_inst_424_, 0);
v_toBind_431_ = lean_ctor_get(v_inst_424_, 1);
lean_inc_n(v_toBind_431_, 3);
v_toPure_432_ = lean_ctor_get(v_toApplicative_430_, 1);
lean_inc_n(v_toPure_432_, 2);
lean_inc(v_inst_425_);
v_x_433_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__1), 3, 1);
lean_closure_set(v_x_433_, 0, v_inst_425_);
v___x_434_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___redArg___closed__2, &l_Lean_Meta_forEachExpr_x27___redArg___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__2);
v___x_435_ = l_Lean_Meta_forEachExpr_x27___redArg___lam__1(v_inst_425_, lean_box(0), v___x_434_);
v___f_436_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_436_, 0, v_toPure_432_);
v___f_437_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__5), 9, 8);
lean_closure_set(v___f_437_, 0, v_toPure_432_);
lean_closure_set(v___f_437_, 1, v_x_433_);
lean_closure_set(v___f_437_, 2, v_toBind_431_);
lean_closure_set(v___f_437_, 3, v_inst_424_);
lean_closure_set(v___f_437_, 4, v_inst_426_);
lean_closure_set(v___f_437_, 5, v_fn_428_);
lean_closure_set(v___f_437_, 6, v_x_429_);
lean_closure_set(v___f_437_, 7, v_input_427_);
v___x_438_ = lean_apply_4(v_toBind_431_, lean_box(0), lean_box(0), v___x_435_, v___f_437_);
v___x_439_ = lean_apply_4(v_toBind_431_, lean_box(0), lean_box(0), v___x_438_, v___f_436_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27(lean_object* v_m_440_, lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_input_444_, lean_object* v_fn_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Meta_forEachExpr_x27___redArg(v_inst_441_, v_inst_442_, v_inst_443_, v_input_444_, v_fn_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg___lam__0(lean_object* v_toPure_447_, lean_object* v_____r_448_){
_start:
{
uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_449_ = 1;
v___x_450_ = lean_box(v___x_449_);
v___x_451_ = lean_apply_2(v_toPure_447_, lean_box(0), v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg___lam__1(lean_object* v_f_452_, lean_object* v_toBind_453_, lean_object* v___f_454_, lean_object* v_e_455_){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_apply_1(v_f_452_, v_e_455_);
v___x_457_ = lean_apply_4(v_toBind_453_, lean_box(0), lean_box(0), v___x_456_, v___f_454_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg(lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_e_461_, lean_object* v_f_462_){
_start:
{
lean_object* v_toApplicative_463_; lean_object* v_toBind_464_; lean_object* v_toPure_465_; lean_object* v___f_466_; lean_object* v___f_467_; lean_object* v___x_468_; 
v_toApplicative_463_ = lean_ctor_get(v_inst_458_, 0);
v_toBind_464_ = lean_ctor_get(v_inst_458_, 1);
v_toPure_465_ = lean_ctor_get(v_toApplicative_463_, 1);
lean_inc(v_toPure_465_);
v___f_466_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___redArg___lam__0), 2, 1);
lean_closure_set(v___f_466_, 0, v_toPure_465_);
lean_inc(v_toBind_464_);
v___f_467_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___redArg___lam__1), 4, 3);
lean_closure_set(v___f_467_, 0, v_f_462_);
lean_closure_set(v___f_467_, 1, v_toBind_464_);
lean_closure_set(v___f_467_, 2, v___f_466_);
v___x_468_ = l_Lean_Meta_forEachExpr_x27___redArg(v_inst_458_, v_inst_459_, v_inst_460_, v_e_461_, v___f_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr(lean_object* v_m_469_, lean_object* v_inst_470_, lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_e_473_, lean_object* v_f_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_Meta_forEachExpr___redArg(v_inst_470_, v_inst_471_, v_inst_472_, v_e_473_, v_f_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0(lean_object* v_toPure_476_, lean_object* v_____do__lift_477_){
_start:
{
lean_object* v_userName_478_; uint8_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v_userName_478_ = lean_ctor_get(v_____do__lift_477_, 0);
v___x_479_ = l_Lean_Name_isAnonymous(v_userName_478_);
v___x_480_ = lean_box(v___x_479_);
v___x_481_ = lean_apply_2(v_toPure_476_, lean_box(0), v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0___boxed(lean_object* v_toPure_482_, lean_object* v_____do__lift_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0(v_toPure_482_, v_____do__lift_483_);
lean_dec_ref(v_____do__lift_483_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg(lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_x_487_){
_start:
{
lean_object* v_toApplicative_488_; 
v_toApplicative_488_ = lean_ctor_get(v_inst_485_, 0);
lean_inc_ref(v_toApplicative_488_);
if (lean_obj_tag(v_x_487_) == 2)
{
lean_object* v_toBind_489_; lean_object* v_toPure_490_; lean_object* v_mvarId_491_; lean_object* v___f_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_toBind_489_ = lean_ctor_get(v_inst_485_, 1);
lean_inc(v_toBind_489_);
lean_dec_ref(v_inst_485_);
v_toPure_490_ = lean_ctor_get(v_toApplicative_488_, 1);
lean_inc(v_toPure_490_);
lean_dec_ref(v_toApplicative_488_);
v_mvarId_491_ = lean_ctor_get(v_x_487_, 0);
lean_inc(v_mvarId_491_);
lean_dec_ref(v_x_487_);
v___f_492_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_492_, 0, v_toPure_490_);
v___x_493_ = lean_alloc_closure((void*)(l_Lean_MVarId_getDecl___boxed), 6, 1);
lean_closure_set(v___x_493_, 0, v_mvarId_491_);
v___x_494_ = lean_apply_2(v_inst_486_, lean_box(0), v___x_493_);
v___x_495_ = lean_apply_4(v_toBind_489_, lean_box(0), lean_box(0), v___x_494_, v___f_492_);
return v___x_495_;
}
else
{
lean_object* v_toPure_496_; uint8_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
lean_dec_ref(v_x_487_);
lean_dec(v_inst_486_);
lean_dec_ref(v_inst_485_);
v_toPure_496_ = lean_ctor_get(v_toApplicative_488_, 1);
lean_inc(v_toPure_496_);
lean_dec_ref(v_toApplicative_488_);
v___x_497_ = 0;
v___x_498_ = lean_box(v___x_497_);
v___x_499_ = lean_apply_2(v_toPure_496_, lean_box(0), v___x_498_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName(lean_object* v_m_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_x_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg(v_inst_501_, v_inst_502_, v_x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0(lean_object* v_k_505_, lean_object* v_b_506_, lean_object* v_c_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v___x_513_; 
lean_inc(v___y_511_);
lean_inc_ref(v___y_510_);
lean_inc(v___y_509_);
lean_inc_ref(v___y_508_);
v___x_513_ = lean_apply_7(v_k_505_, v_b_506_, v_c_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, lean_box(0));
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0___boxed(lean_object* v_k_514_, lean_object* v_b_515_, lean_object* v_c_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0(v_k_514_, v_b_515_, v_c_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(lean_object* v_type_523_, lean_object* v_maxFVars_x3f_524_, lean_object* v_k_525_, uint8_t v_cleanupAnnotations_526_, uint8_t v_whnfType_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___f_533_; lean_object* v___x_534_; 
v___f_533_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_533_, 0, v_k_525_);
v___x_534_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_523_, v_maxFVars_x3f_524_, v___f_533_, v_cleanupAnnotations_526_, v_whnfType_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_534_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
v_a_543_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_534_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_534_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___boxed(lean_object* v_type_551_, lean_object* v_maxFVars_x3f_552_, lean_object* v_k_553_, lean_object* v_cleanupAnnotations_554_, lean_object* v_whnfType_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_561_; uint8_t v_whnfType_boxed_562_; lean_object* v_res_563_; 
v_cleanupAnnotations_boxed_561_ = lean_unbox(v_cleanupAnnotations_554_);
v_whnfType_boxed_562_ = lean_unbox(v_whnfType_555_);
v_res_563_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(v_type_551_, v_maxFVars_x3f_552_, v_k_553_, v_cleanupAnnotations_boxed_561_, v_whnfType_boxed_562_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0(lean_object* v_00_u03b1_564_, lean_object* v_type_565_, lean_object* v_maxFVars_x3f_566_, lean_object* v_k_567_, uint8_t v_cleanupAnnotations_568_, uint8_t v_whnfType_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(v_type_565_, v_maxFVars_x3f_566_, v_k_567_, v_cleanupAnnotations_568_, v_whnfType_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___boxed(lean_object* v_00_u03b1_576_, lean_object* v_type_577_, lean_object* v_maxFVars_x3f_578_, lean_object* v_k_579_, lean_object* v_cleanupAnnotations_580_, lean_object* v_whnfType_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_587_; uint8_t v_whnfType_boxed_588_; lean_object* v_res_589_; 
v_cleanupAnnotations_boxed_587_ = lean_unbox(v_cleanupAnnotations_580_);
v_whnfType_boxed_588_ = lean_unbox(v_whnfType_581_);
v_res_589_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0(v_00_u03b1_576_, v_type_577_, v_maxFVars_x3f_578_, v_k_579_, v_cleanupAnnotations_boxed_587_, v_whnfType_boxed_588_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(lean_object* v_e_590_, lean_object* v___y_591_){
_start:
{
uint8_t v___x_593_; 
v___x_593_ = l_Lean_Expr_hasMVar(v_e_590_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
v___x_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_594_, 0, v_e_590_);
return v___x_594_;
}
else
{
lean_object* v___x_595_; lean_object* v_mctx_596_; lean_object* v___x_597_; lean_object* v_fst_598_; lean_object* v_snd_599_; lean_object* v___x_600_; lean_object* v_cache_601_; lean_object* v_zetaDeltaFVarIds_602_; lean_object* v_postponed_603_; lean_object* v_diag_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_613_; 
v___x_595_ = lean_st_ref_get(v___y_591_);
v_mctx_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc_ref(v_mctx_596_);
lean_dec(v___x_595_);
v___x_597_ = l_Lean_instantiateMVarsCore(v_mctx_596_, v_e_590_);
v_fst_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_fst_598_);
v_snd_599_ = lean_ctor_get(v___x_597_, 1);
lean_inc(v_snd_599_);
lean_dec_ref(v___x_597_);
v___x_600_ = lean_st_ref_take(v___y_591_);
v_cache_601_ = lean_ctor_get(v___x_600_, 1);
v_zetaDeltaFVarIds_602_ = lean_ctor_get(v___x_600_, 2);
v_postponed_603_ = lean_ctor_get(v___x_600_, 3);
v_diag_604_ = lean_ctor_get(v___x_600_, 4);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; 
v_unused_614_ = lean_ctor_get(v___x_600_, 0);
lean_dec(v_unused_614_);
v___x_606_ = v___x_600_;
v_isShared_607_ = v_isSharedCheck_613_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_diag_604_);
lean_inc(v_postponed_603_);
lean_inc(v_zetaDeltaFVarIds_602_);
lean_inc(v_cache_601_);
lean_dec(v___x_600_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_613_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v_snd_599_);
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_snd_599_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_cache_601_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v_zetaDeltaFVarIds_602_);
lean_ctor_set(v_reuseFailAlloc_612_, 3, v_postponed_603_);
lean_ctor_set(v_reuseFailAlloc_612_, 4, v_diag_604_);
v___x_609_ = v_reuseFailAlloc_612_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_st_ref_set(v___y_591_, v___x_609_);
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v_fst_598_);
return v___x_611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg___boxed(lean_object* v_e_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(v_e_615_, v___y_616_);
lean_dec(v___y_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3(lean_object* v_e_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(v_e_619_, v___y_621_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___boxed(lean_object* v_e_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3(v_e_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0(lean_object* v_a_633_, lean_object* v___x_634_, lean_object* v_val_635_, lean_object* v___x_636_, lean_object* v_xs_637_, lean_object* v_x_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_644_ = lean_array_get_size(v_xs_637_);
v___x_645_ = lean_nat_dec_lt(v_a_633_, v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
lean_dec(v___x_636_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_634_);
return v___x_646_;
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = l_Lean_instInhabitedExpr;
v___x_648_ = lean_array_get_borrowed(v___x_647_, v_xs_637_, v_a_633_);
v___x_649_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_648_, v___y_639_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref(v___x_649_);
v___x_651_ = l_Lean_LocalDecl_userName(v_a_650_);
lean_dec(v_a_650_);
v___x_652_ = l_Lean_Core_mkFreshUserName(v___x_651_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_678_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_678_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_678_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_678_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v_mctx_661_; lean_object* v_cache_662_; lean_object* v_zetaDeltaFVarIds_663_; lean_object* v_postponed_664_; lean_object* v_diag_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_677_; 
v___x_657_ = lean_st_ref_take(v_val_635_);
lean_inc(v___x_636_);
v___x_658_ = lean_array_push(v___x_657_, v___x_636_);
v___x_659_ = lean_st_ref_set(v_val_635_, v___x_658_);
v___x_660_ = lean_st_ref_take(v___y_640_);
v_mctx_661_ = lean_ctor_get(v___x_660_, 0);
v_cache_662_ = lean_ctor_get(v___x_660_, 1);
v_zetaDeltaFVarIds_663_ = lean_ctor_get(v___x_660_, 2);
v_postponed_664_ = lean_ctor_get(v___x_660_, 3);
v_diag_665_ = lean_ctor_get(v___x_660_, 4);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_677_ == 0)
{
v___x_667_ = v___x_660_;
v_isShared_668_ = v_isSharedCheck_677_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_diag_665_);
lean_inc(v_postponed_664_);
lean_inc(v_zetaDeltaFVarIds_663_);
lean_inc(v_cache_662_);
lean_inc(v_mctx_661_);
lean_dec(v___x_660_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_677_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_669_ = l_Lean_MetavarContext_setMVarUserNameTemporarily(v_mctx_661_, v___x_636_, v_a_653_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_669_);
v___x_671_ = v___x_667_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_cache_662_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_zetaDeltaFVarIds_663_);
lean_ctor_set(v_reuseFailAlloc_676_, 3, v_postponed_664_);
lean_ctor_set(v_reuseFailAlloc_676_, 4, v_diag_665_);
v___x_671_ = v_reuseFailAlloc_676_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = lean_st_ref_set(v___y_640_, v___x_671_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_634_);
v___x_674_ = v___x_655_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_634_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec(v___x_636_);
v_a_679_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_652_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_652_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_dec(v___x_636_);
v_a_687_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_649_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_649_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0___boxed(lean_object* v_a_695_, lean_object* v___x_696_, lean_object* v_val_697_, lean_object* v___x_698_, lean_object* v_xs_699_, lean_object* v_x_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0(v_a_695_, v___x_696_, v_val_697_, v___x_698_, v_xs_699_, v_x_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec_ref(v_x_700_);
lean_dec_ref(v_xs_699_);
lean_dec(v_val_697_);
lean_dec(v_a_695_);
return v_res_706_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(lean_object* v_a_707_, lean_object* v_as_708_, size_t v_i_709_, size_t v_stop_710_){
_start:
{
uint8_t v___x_711_; 
v___x_711_ = lean_usize_dec_eq(v_i_709_, v_stop_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = lean_array_uget_borrowed(v_as_708_, v_i_709_);
v___x_713_ = lean_expr_eqv(v_a_707_, v___x_712_);
if (v___x_713_ == 0)
{
size_t v___x_714_; size_t v___x_715_; 
v___x_714_ = ((size_t)1ULL);
v___x_715_ = lean_usize_add(v_i_709_, v___x_714_);
v_i_709_ = v___x_715_;
goto _start;
}
else
{
return v___x_713_;
}
}
else
{
uint8_t v___x_717_; 
v___x_717_ = 0;
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1___boxed(lean_object* v_a_718_, lean_object* v_as_719_, lean_object* v_i_720_, lean_object* v_stop_721_){
_start:
{
size_t v_i_boxed_722_; size_t v_stop_boxed_723_; uint8_t v_res_724_; lean_object* v_r_725_; 
v_i_boxed_722_ = lean_unbox_usize(v_i_720_);
lean_dec(v_i_720_);
v_stop_boxed_723_ = lean_unbox_usize(v_stop_721_);
lean_dec(v_stop_721_);
v_res_724_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(v_a_718_, v_as_719_, v_i_boxed_722_, v_stop_boxed_723_);
lean_dec_ref(v_as_719_);
lean_dec_ref(v_a_718_);
v_r_725_ = lean_box(v_res_724_);
return v_r_725_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(lean_object* v_as_726_, lean_object* v_a_727_){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_728_ = lean_unsigned_to_nat(0u);
v___x_729_ = lean_array_get_size(v_as_726_);
v___x_730_ = lean_nat_dec_lt(v___x_728_, v___x_729_);
if (v___x_730_ == 0)
{
return v___x_730_;
}
else
{
if (v___x_730_ == 0)
{
return v___x_730_;
}
else
{
size_t v___x_731_; size_t v___x_732_; uint8_t v___x_733_; 
v___x_731_ = ((size_t)0ULL);
v___x_732_ = lean_usize_of_nat(v___x_729_);
v___x_733_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(v_a_727_, v_as_726_, v___x_731_, v___x_732_);
return v___x_733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1___boxed(lean_object* v_as_734_, lean_object* v_a_735_){
_start:
{
uint8_t v_res_736_; lean_object* v_r_737_; 
v_res_736_ = l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(v_as_734_, v_a_735_);
lean_dec_ref(v_a_735_);
lean_dec_ref(v_as_734_);
v_r_737_ = lean_box(v_res_736_);
return v_r_737_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(lean_object* v_upperBound_738_, lean_object* v___x_739_, lean_object* v_val_740_, lean_object* v_e_741_, lean_object* v_isTarget_742_, lean_object* v_a_743_, lean_object* v_b_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_a_751_; uint8_t v___x_755_; 
v___x_755_ = lean_nat_dec_lt(v_a_743_, v_upperBound_738_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; 
lean_dec(v_a_743_);
lean_dec(v_val_740_);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v_b_744_);
return v___x_756_;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; uint8_t v___y_760_; uint8_t v___x_791_; 
v___x_757_ = lean_box(0);
v___x_758_ = lean_array_fget_borrowed(v___x_739_, v_a_743_);
v___x_791_ = l_Lean_Expr_isMVar(v___x_758_);
if (v___x_791_ == 0)
{
v___y_760_ = v___x_791_;
goto v___jp_759_;
}
else
{
uint8_t v___x_792_; 
v___x_792_ = l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(v_isTarget_742_, v___x_758_);
v___y_760_ = v___x_792_;
goto v___jp_759_;
}
v___jp_759_:
{
if (v___y_760_ == 0)
{
v_a_751_ = v___x_757_;
goto v___jp_750_;
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = l_Lean_Expr_mvarId_x21(v___x_758_);
lean_inc(v___x_761_);
v___x_762_ = l_Lean_MVarId_getDecl(v___x_761_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v_userName_764_; uint8_t v___x_765_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref(v___x_762_);
v_userName_764_ = lean_ctor_get(v_a_763_, 0);
lean_inc(v_userName_764_);
lean_dec(v_a_763_);
v___x_765_ = l_Lean_Name_isAnonymous(v_userName_764_);
lean_dec(v_userName_764_);
if (v___x_765_ == 0)
{
lean_dec(v___x_761_);
v_a_751_ = v___x_757_;
goto v___jp_750_;
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = l_Lean_Expr_getAppFn(v_e_741_);
lean_inc(v___y_748_);
lean_inc_ref(v___y_747_);
lean_inc(v___y_746_);
lean_inc_ref(v___y_745_);
v___x_767_ = lean_infer_type(v___x_766_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___f_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; lean_object* v___x_774_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref(v___x_767_);
lean_inc(v_val_740_);
lean_inc(v_a_743_);
v___f_769_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_769_, 0, v_a_743_);
lean_closure_set(v___f_769_, 1, v___x_757_);
lean_closure_set(v___f_769_, 2, v_val_740_);
lean_closure_set(v___f_769_, 3, v___x_761_);
v___x_770_ = lean_unsigned_to_nat(1u);
v___x_771_ = lean_nat_add(v_a_743_, v___x_770_);
v___x_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
v___x_773_ = 0;
v___x_774_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(v_a_768_, v___x_772_, v___f_769_, v___x_773_, v___x_773_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_dec_ref(v___x_774_);
v_a_751_ = v___x_757_;
goto v___jp_750_;
}
else
{
lean_dec(v_a_743_);
lean_dec(v_val_740_);
return v___x_774_;
}
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec(v___x_761_);
lean_dec(v_a_743_);
lean_dec(v_val_740_);
v_a_775_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_767_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_767_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
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
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec(v___x_761_);
lean_dec(v_a_743_);
lean_dec(v_val_740_);
v_a_783_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_762_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_762_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
v___jp_750_:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_unsigned_to_nat(1u);
v___x_753_ = lean_nat_add(v_a_743_, v___x_752_);
lean_dec(v_a_743_);
v_a_743_ = v___x_753_;
v_b_744_ = v_a_751_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___boxed(lean_object* v_upperBound_793_, lean_object* v___x_794_, lean_object* v_val_795_, lean_object* v_e_796_, lean_object* v_isTarget_797_, lean_object* v_a_798_, lean_object* v_b_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(v_upperBound_793_, v___x_794_, v_val_795_, v_e_796_, v_isTarget_797_, v_a_798_, v_b_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec_ref(v_isTarget_797_);
lean_dec_ref(v_e_796_);
lean_dec_ref(v___x_794_);
lean_dec(v_upperBound_793_);
return v_res_805_;
}
}
static lean_object* _init_l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0(void){
_start:
{
lean_object* v___x_806_; lean_object* v_dummy_807_; 
v___x_806_ = lean_box(0);
v_dummy_807_ = l_Lean_Expr_sort___override(v___x_806_);
return v_dummy_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___lam__0(lean_object* v_val_808_, lean_object* v_isTarget_809_, lean_object* v___x_810_, lean_object* v_e_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
uint8_t v___x_817_; 
v___x_817_ = l_Lean_Expr_isApp(v_e_811_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec_ref(v_e_811_);
lean_dec(v___x_810_);
lean_dec(v_val_808_);
v___x_818_ = lean_box(0);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
else
{
lean_object* v_dummy_820_; lean_object* v_nargs_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v_dummy_820_ = lean_obj_once(&l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0, &l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0_once, _init_l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0);
v_nargs_821_ = l_Lean_Expr_getAppNumArgs(v_e_811_);
lean_inc(v_nargs_821_);
v___x_822_ = lean_mk_array(v_nargs_821_, v_dummy_820_);
v___x_823_ = lean_unsigned_to_nat(1u);
v___x_824_ = lean_nat_sub(v_nargs_821_, v___x_823_);
lean_dec(v_nargs_821_);
lean_inc_ref(v_e_811_);
v___x_825_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_811_, v___x_822_, v___x_824_);
v___x_826_ = lean_array_get_size(v___x_825_);
v___x_827_ = lean_box(0);
v___x_828_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(v___x_826_, v___x_825_, v_val_808_, v_e_811_, v_isTarget_809_, v___x_810_, v___x_827_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
lean_dec_ref(v_e_811_);
lean_dec_ref(v___x_825_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; 
v_unused_836_ = lean_ctor_get(v___x_828_, 0);
lean_dec(v_unused_836_);
v___x_830_ = v___x_828_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_dec(v___x_828_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_827_);
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_827_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
else
{
return v___x_828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___lam__0___boxed(lean_object* v_val_837_, lean_object* v_isTarget_838_, lean_object* v___x_839_, lean_object* v_e_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_Meta_setMVarUserNamesAt___lam__0(v_val_837_, v_isTarget_838_, v___x_839_, v_e_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec_ref(v_isTarget_838_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0(lean_object* v_k_847_, lean_object* v___y_848_, lean_object* v_b_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v___x_855_; 
lean_inc(v___y_853_);
lean_inc_ref(v___y_852_);
lean_inc(v___y_851_);
lean_inc_ref(v___y_850_);
lean_inc(v___y_848_);
v___x_855_ = lean_apply_7(v_k_847_, v_b_849_, v___y_848_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, lean_box(0));
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0___boxed(lean_object* v_k_856_, lean_object* v___y_857_, lean_object* v_b_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0(v_k_856_, v___y_857_, v_b_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_857_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(lean_object* v_name_865_, uint8_t v_bi_866_, lean_object* v_type_867_, lean_object* v_k_868_, uint8_t v_kind_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___f_876_; lean_object* v___x_877_; 
lean_inc(v___y_870_);
v___f_876_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_876_, 0, v_k_868_);
lean_closure_set(v___f_876_, 1, v___y_870_);
v___x_877_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_865_, v_bi_866_, v_type_867_, v___f_876_, v_kind_869_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_877_) == 0)
{
return v___x_877_;
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_877_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_877_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___boxed(lean_object* v_name_886_, lean_object* v_bi_887_, lean_object* v_type_888_, lean_object* v_k_889_, lean_object* v_kind_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
uint8_t v_bi_boxed_897_; uint8_t v_kind_boxed_898_; lean_object* v_res_899_; 
v_bi_boxed_897_ = lean_unbox(v_bi_887_);
v_kind_boxed_898_ = lean_unbox(v_kind_890_);
v_res_899_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_name_886_, v_bi_boxed_897_, v_type_888_, v_k_889_, v_kind_boxed_898_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0___boxed(lean_object* v_fvars_900_, lean_object* v_f_901_, lean_object* v_body_902_, lean_object* v_x_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0(v_fvars_900_, v_f_901_, v_body_902_, v_x_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(lean_object* v_f_911_, lean_object* v_fvars_912_, lean_object* v_a_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
if (lean_obj_tag(v_a_913_) == 6)
{
lean_object* v_binderName_920_; lean_object* v_binderType_921_; lean_object* v_body_922_; uint8_t v_binderInfo_923_; lean_object* v_d_924_; lean_object* v___x_925_; 
v_binderName_920_ = lean_ctor_get(v_a_913_, 0);
lean_inc(v_binderName_920_);
v_binderType_921_ = lean_ctor_get(v_a_913_, 1);
lean_inc_ref(v_binderType_921_);
v_body_922_ = lean_ctor_get(v_a_913_, 2);
lean_inc_ref(v_body_922_);
v_binderInfo_923_ = lean_ctor_get_uint8(v_a_913_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_913_);
v_d_924_ = lean_expr_instantiate_rev(v_binderType_921_, v_fvars_912_);
lean_dec_ref(v_binderType_921_);
lean_inc_ref(v_f_911_);
lean_inc(v___y_918_);
lean_inc_ref(v___y_917_);
lean_inc(v___y_916_);
lean_inc_ref(v___y_915_);
lean_inc(v___y_914_);
lean_inc_ref(v_d_924_);
v___x_925_ = lean_apply_7(v_f_911_, v_d_924_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, lean_box(0));
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v___f_926_; uint8_t v___x_927_; lean_object* v___x_928_; 
lean_dec_ref(v___x_925_);
v___f_926_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0___boxed), 10, 3);
lean_closure_set(v___f_926_, 0, v_fvars_912_);
lean_closure_set(v___f_926_, 1, v_f_911_);
lean_closure_set(v___f_926_, 2, v_body_922_);
v___x_927_ = 0;
v___x_928_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_binderName_920_, v_binderInfo_923_, v_d_924_, v___f_926_, v___x_927_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
return v___x_928_;
}
else
{
lean_dec_ref(v_d_924_);
lean_dec_ref(v_body_922_);
lean_dec(v_binderName_920_);
lean_dec_ref(v_fvars_912_);
lean_dec_ref(v_f_911_);
return v___x_925_;
}
}
else
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = lean_expr_instantiate_rev(v_a_913_, v_fvars_912_);
lean_dec_ref(v_fvars_912_);
lean_dec_ref(v_a_913_);
lean_inc(v___y_918_);
lean_inc_ref(v___y_917_);
lean_inc(v___y_916_);
lean_inc_ref(v___y_915_);
lean_inc(v___y_914_);
v___x_930_ = lean_apply_7(v_f_911_, v___x_929_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, lean_box(0));
return v___x_930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0(lean_object* v_fvars_931_, lean_object* v_f_932_, lean_object* v_body_933_, lean_object* v_x_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = lean_array_push(v_fvars_931_, v_x_934_);
v___x_942_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(v_f_932_, v___x_941_, v_body_933_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___boxed(lean_object* v_f_943_, lean_object* v_fvars_944_, lean_object* v_a_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(v_f_943_, v_fvars_944_, v_a_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(lean_object* v_f_953_, lean_object* v_e_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_962_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(v_f_953_, v___x_961_, v_e_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10___boxed(lean_object* v_f_963_, lean_object* v_e_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(v_f_963_, v_e_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_object* v_00_u03b1_972_, lean_object* v_x_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_apply_1(v_x_973_, lean_box(0));
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0___boxed(lean_object* v_00_u03b1_981_, lean_object* v_x_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(v_00_u03b1_981_, v_x_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0___boxed(lean_object* v_fvars_989_, lean_object* v_f_990_, lean_object* v_body_991_, lean_object* v_x_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0(v_fvars_989_, v_f_990_, v_body_991_, v_x_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(lean_object* v_f_1000_, lean_object* v_fvars_1001_, lean_object* v_a_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
if (lean_obj_tag(v_a_1002_) == 7)
{
lean_object* v_binderName_1009_; lean_object* v_binderType_1010_; lean_object* v_body_1011_; uint8_t v_binderInfo_1012_; lean_object* v_d_1013_; lean_object* v___x_1014_; 
v_binderName_1009_ = lean_ctor_get(v_a_1002_, 0);
lean_inc(v_binderName_1009_);
v_binderType_1010_ = lean_ctor_get(v_a_1002_, 1);
lean_inc_ref(v_binderType_1010_);
v_body_1011_ = lean_ctor_get(v_a_1002_, 2);
lean_inc_ref(v_body_1011_);
v_binderInfo_1012_ = lean_ctor_get_uint8(v_a_1002_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_1002_);
v_d_1013_ = lean_expr_instantiate_rev(v_binderType_1010_, v_fvars_1001_);
lean_dec_ref(v_binderType_1010_);
lean_inc_ref(v_f_1000_);
lean_inc(v___y_1007_);
lean_inc_ref(v___y_1006_);
lean_inc(v___y_1005_);
lean_inc_ref(v___y_1004_);
lean_inc(v___y_1003_);
lean_inc_ref(v_d_1013_);
v___x_1014_ = lean_apply_7(v_f_1000_, v_d_1013_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, lean_box(0));
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v___f_1015_; uint8_t v___x_1016_; lean_object* v___x_1017_; 
lean_dec_ref(v___x_1014_);
v___f_1015_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1015_, 0, v_fvars_1001_);
lean_closure_set(v___f_1015_, 1, v_f_1000_);
lean_closure_set(v___f_1015_, 2, v_body_1011_);
v___x_1016_ = 0;
v___x_1017_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_binderName_1009_, v_binderInfo_1012_, v_d_1013_, v___f_1015_, v___x_1016_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
return v___x_1017_;
}
else
{
lean_dec_ref(v_d_1013_);
lean_dec_ref(v_body_1011_);
lean_dec(v_binderName_1009_);
lean_dec_ref(v_fvars_1001_);
lean_dec_ref(v_f_1000_);
return v___x_1014_;
}
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_expr_instantiate_rev(v_a_1002_, v_fvars_1001_);
lean_dec_ref(v_fvars_1001_);
lean_dec_ref(v_a_1002_);
lean_inc(v___y_1007_);
lean_inc_ref(v___y_1006_);
lean_inc(v___y_1005_);
lean_inc_ref(v___y_1004_);
lean_inc(v___y_1003_);
v___x_1019_ = lean_apply_7(v_f_1000_, v___x_1018_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, lean_box(0));
return v___x_1019_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0(lean_object* v_fvars_1020_, lean_object* v_f_1021_, lean_object* v_body_1022_, lean_object* v_x_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_array_push(v_fvars_1020_, v_x_1023_);
v___x_1031_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(v_f_1021_, v___x_1030_, v_body_1022_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___boxed(lean_object* v_f_1032_, lean_object* v_fvars_1033_, lean_object* v_a_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(v_f_1032_, v_fvars_1033_, v_a_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(lean_object* v_f_1042_, lean_object* v_e_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_1051_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(v_f_1042_, v___x_1050_, v_e_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9___boxed(lean_object* v_f_1052_, lean_object* v_e_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(v_f_1052_, v_e_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_a_1061_, lean_object* v_x_1062_){
_start:
{
if (lean_obj_tag(v_x_1062_) == 0)
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_box(0);
return v___x_1063_;
}
else
{
lean_object* v_key_1064_; lean_object* v_value_1065_; lean_object* v_tail_1066_; uint8_t v___x_1067_; 
v_key_1064_ = lean_ctor_get(v_x_1062_, 0);
v_value_1065_ = lean_ctor_get(v_x_1062_, 1);
v_tail_1066_ = lean_ctor_get(v_x_1062_, 2);
v___x_1067_ = lean_expr_eqv(v_key_1064_, v_a_1061_);
if (v___x_1067_ == 0)
{
v_x_1062_ = v_tail_1066_;
goto _start;
}
else
{
lean_object* v___x_1069_; 
lean_inc(v_value_1065_);
v___x_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1069_, 0, v_value_1065_);
return v___x_1069_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_a_1070_, lean_object* v_x_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(v_a_1070_, v_x_1071_);
lean_dec(v_x_1071_);
lean_dec_ref(v_a_1070_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_m_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_buckets_1075_; lean_object* v___x_1076_; uint64_t v___x_1077_; uint64_t v___x_1078_; uint64_t v___x_1079_; uint64_t v_fold_1080_; uint64_t v___x_1081_; uint64_t v___x_1082_; uint64_t v___x_1083_; size_t v___x_1084_; size_t v___x_1085_; size_t v___x_1086_; size_t v___x_1087_; size_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_buckets_1075_ = lean_ctor_get(v_m_1073_, 1);
v___x_1076_ = lean_array_get_size(v_buckets_1075_);
v___x_1077_ = l_Lean_Expr_hash(v_a_1074_);
v___x_1078_ = 32ULL;
v___x_1079_ = lean_uint64_shift_right(v___x_1077_, v___x_1078_);
v_fold_1080_ = lean_uint64_xor(v___x_1077_, v___x_1079_);
v___x_1081_ = 16ULL;
v___x_1082_ = lean_uint64_shift_right(v_fold_1080_, v___x_1081_);
v___x_1083_ = lean_uint64_xor(v_fold_1080_, v___x_1082_);
v___x_1084_ = lean_uint64_to_usize(v___x_1083_);
v___x_1085_ = lean_usize_of_nat(v___x_1076_);
v___x_1086_ = ((size_t)1ULL);
v___x_1087_ = lean_usize_sub(v___x_1085_, v___x_1086_);
v___x_1088_ = lean_usize_land(v___x_1084_, v___x_1087_);
v___x_1089_ = lean_array_uget_borrowed(v_buckets_1075_, v___x_1088_);
v___x_1090_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(v_a_1074_, v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_m_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_m_1091_, v_a_1092_);
lean_dec_ref(v_a_1092_);
lean_dec_ref(v_m_1091_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(lean_object* v_a_1094_, lean_object* v_b_1095_, lean_object* v_x_1096_){
_start:
{
if (lean_obj_tag(v_x_1096_) == 0)
{
lean_dec(v_b_1095_);
lean_dec_ref(v_a_1094_);
return v_x_1096_;
}
else
{
lean_object* v_key_1097_; lean_object* v_value_1098_; lean_object* v_tail_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1111_; 
v_key_1097_ = lean_ctor_get(v_x_1096_, 0);
v_value_1098_ = lean_ctor_get(v_x_1096_, 1);
v_tail_1099_ = lean_ctor_get(v_x_1096_, 2);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_x_1096_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1101_ = v_x_1096_;
v_isShared_1102_ = v_isSharedCheck_1111_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_tail_1099_);
lean_inc(v_value_1098_);
lean_inc(v_key_1097_);
lean_dec(v_x_1096_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1111_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
uint8_t v___x_1103_; 
v___x_1103_ = lean_expr_eqv(v_key_1097_, v_a_1094_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1104_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(v_a_1094_, v_b_1095_, v_tail_1099_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 2, v___x_1104_);
v___x_1106_ = v___x_1101_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_key_1097_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_value_1098_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
else
{
lean_object* v___x_1109_; 
lean_dec(v_value_1098_);
lean_dec(v_key_1097_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 1, v_b_1095_);
lean_ctor_set(v___x_1101_, 0, v_a_1094_);
v___x_1109_ = v___x_1101_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1094_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_b_1095_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v_tail_1099_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16___redArg(lean_object* v_x_1112_, lean_object* v_x_1113_){
_start:
{
if (lean_obj_tag(v_x_1113_) == 0)
{
return v_x_1112_;
}
else
{
lean_object* v_key_1114_; lean_object* v_value_1115_; lean_object* v_tail_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1139_; 
v_key_1114_ = lean_ctor_get(v_x_1113_, 0);
v_value_1115_ = lean_ctor_get(v_x_1113_, 1);
v_tail_1116_ = lean_ctor_get(v_x_1113_, 2);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_x_1113_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1118_ = v_x_1113_;
v_isShared_1119_ = v_isSharedCheck_1139_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_tail_1116_);
lean_inc(v_value_1115_);
lean_inc(v_key_1114_);
lean_dec(v_x_1113_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1139_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; uint64_t v___x_1121_; uint64_t v___x_1122_; uint64_t v___x_1123_; uint64_t v_fold_1124_; uint64_t v___x_1125_; uint64_t v___x_1126_; uint64_t v___x_1127_; size_t v___x_1128_; size_t v___x_1129_; size_t v___x_1130_; size_t v___x_1131_; size_t v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1120_ = lean_array_get_size(v_x_1112_);
v___x_1121_ = l_Lean_Expr_hash(v_key_1114_);
v___x_1122_ = 32ULL;
v___x_1123_ = lean_uint64_shift_right(v___x_1121_, v___x_1122_);
v_fold_1124_ = lean_uint64_xor(v___x_1121_, v___x_1123_);
v___x_1125_ = 16ULL;
v___x_1126_ = lean_uint64_shift_right(v_fold_1124_, v___x_1125_);
v___x_1127_ = lean_uint64_xor(v_fold_1124_, v___x_1126_);
v___x_1128_ = lean_uint64_to_usize(v___x_1127_);
v___x_1129_ = lean_usize_of_nat(v___x_1120_);
v___x_1130_ = ((size_t)1ULL);
v___x_1131_ = lean_usize_sub(v___x_1129_, v___x_1130_);
v___x_1132_ = lean_usize_land(v___x_1128_, v___x_1131_);
v___x_1133_ = lean_array_uget_borrowed(v_x_1112_, v___x_1132_);
lean_inc(v___x_1133_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 2, v___x_1133_);
v___x_1135_ = v___x_1118_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_key_1114_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_value_1115_);
lean_ctor_set(v_reuseFailAlloc_1138_, 2, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_array_uset(v_x_1112_, v___x_1132_, v___x_1135_);
v_x_1112_ = v___x_1136_;
v_x_1113_ = v_tail_1116_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12___redArg(lean_object* v_i_1140_, lean_object* v_source_1141_, lean_object* v_target_1142_){
_start:
{
lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = lean_array_get_size(v_source_1141_);
v___x_1144_ = lean_nat_dec_lt(v_i_1140_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_dec_ref(v_source_1141_);
lean_dec(v_i_1140_);
return v_target_1142_;
}
else
{
lean_object* v_es_1145_; lean_object* v___x_1146_; lean_object* v_source_1147_; lean_object* v_target_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v_es_1145_ = lean_array_fget(v_source_1141_, v_i_1140_);
v___x_1146_ = lean_box(0);
v_source_1147_ = lean_array_fset(v_source_1141_, v_i_1140_, v___x_1146_);
v_target_1148_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16___redArg(v_target_1142_, v_es_1145_);
v___x_1149_ = lean_unsigned_to_nat(1u);
v___x_1150_ = lean_nat_add(v_i_1140_, v___x_1149_);
lean_dec(v_i_1140_);
v_i_1140_ = v___x_1150_;
v_source_1141_ = v_source_1147_;
v_target_1142_ = v_target_1148_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11___redArg(lean_object* v_data_1152_){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v_nbuckets_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1153_ = lean_array_get_size(v_data_1152_);
v___x_1154_ = lean_unsigned_to_nat(2u);
v_nbuckets_1155_ = lean_nat_mul(v___x_1153_, v___x_1154_);
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = lean_box(0);
v___x_1158_ = lean_mk_array(v_nbuckets_1155_, v___x_1157_);
v___x_1159_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12___redArg(v___x_1156_, v_data_1152_, v___x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(lean_object* v_a_1160_, lean_object* v_x_1161_){
_start:
{
if (lean_obj_tag(v_x_1161_) == 0)
{
uint8_t v___x_1162_; 
v___x_1162_ = 0;
return v___x_1162_;
}
else
{
lean_object* v_key_1163_; lean_object* v_tail_1164_; uint8_t v___x_1165_; 
v_key_1163_ = lean_ctor_get(v_x_1161_, 0);
v_tail_1164_ = lean_ctor_get(v_x_1161_, 2);
v___x_1165_ = lean_expr_eqv(v_key_1163_, v_a_1160_);
if (v___x_1165_ == 0)
{
v_x_1161_ = v_tail_1164_;
goto _start;
}
else
{
return v___x_1165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_a_1167_, lean_object* v_x_1168_){
_start:
{
uint8_t v_res_1169_; lean_object* v_r_1170_; 
v_res_1169_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_a_1167_, v_x_1168_);
lean_dec(v_x_1168_);
lean_dec_ref(v_a_1167_);
v_r_1170_ = lean_box(v_res_1169_);
return v_r_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(lean_object* v_m_1171_, lean_object* v_a_1172_, lean_object* v_b_1173_){
_start:
{
lean_object* v_size_1174_; lean_object* v_buckets_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1218_; 
v_size_1174_ = lean_ctor_get(v_m_1171_, 0);
v_buckets_1175_ = lean_ctor_get(v_m_1171_, 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_m_1171_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1177_ = v_m_1171_;
v_isShared_1178_ = v_isSharedCheck_1218_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_buckets_1175_);
lean_inc(v_size_1174_);
lean_dec(v_m_1171_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1218_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; uint64_t v___x_1180_; uint64_t v___x_1181_; uint64_t v___x_1182_; uint64_t v_fold_1183_; uint64_t v___x_1184_; uint64_t v___x_1185_; uint64_t v___x_1186_; size_t v___x_1187_; size_t v___x_1188_; size_t v___x_1189_; size_t v___x_1190_; size_t v___x_1191_; lean_object* v_bkt_1192_; uint8_t v___x_1193_; 
v___x_1179_ = lean_array_get_size(v_buckets_1175_);
v___x_1180_ = l_Lean_Expr_hash(v_a_1172_);
v___x_1181_ = 32ULL;
v___x_1182_ = lean_uint64_shift_right(v___x_1180_, v___x_1181_);
v_fold_1183_ = lean_uint64_xor(v___x_1180_, v___x_1182_);
v___x_1184_ = 16ULL;
v___x_1185_ = lean_uint64_shift_right(v_fold_1183_, v___x_1184_);
v___x_1186_ = lean_uint64_xor(v_fold_1183_, v___x_1185_);
v___x_1187_ = lean_uint64_to_usize(v___x_1186_);
v___x_1188_ = lean_usize_of_nat(v___x_1179_);
v___x_1189_ = ((size_t)1ULL);
v___x_1190_ = lean_usize_sub(v___x_1188_, v___x_1189_);
v___x_1191_ = lean_usize_land(v___x_1187_, v___x_1190_);
v_bkt_1192_ = lean_array_uget_borrowed(v_buckets_1175_, v___x_1191_);
v___x_1193_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_a_1172_, v_bkt_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; lean_object* v_size_x27_1195_; lean_object* v___x_1196_; lean_object* v_buckets_x27_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1194_ = lean_unsigned_to_nat(1u);
v_size_x27_1195_ = lean_nat_add(v_size_1174_, v___x_1194_);
lean_dec(v_size_1174_);
lean_inc(v_bkt_1192_);
v___x_1196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1196_, 0, v_a_1172_);
lean_ctor_set(v___x_1196_, 1, v_b_1173_);
lean_ctor_set(v___x_1196_, 2, v_bkt_1192_);
v_buckets_x27_1197_ = lean_array_uset(v_buckets_1175_, v___x_1191_, v___x_1196_);
v___x_1198_ = lean_unsigned_to_nat(4u);
v___x_1199_ = lean_nat_mul(v_size_x27_1195_, v___x_1198_);
v___x_1200_ = lean_unsigned_to_nat(3u);
v___x_1201_ = lean_nat_div(v___x_1199_, v___x_1200_);
lean_dec(v___x_1199_);
v___x_1202_ = lean_array_get_size(v_buckets_x27_1197_);
v___x_1203_ = lean_nat_dec_le(v___x_1201_, v___x_1202_);
lean_dec(v___x_1201_);
if (v___x_1203_ == 0)
{
lean_object* v_val_1204_; lean_object* v___x_1206_; 
v_val_1204_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11___redArg(v_buckets_x27_1197_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v_val_1204_);
lean_ctor_set(v___x_1177_, 0, v_size_x27_1195_);
v___x_1206_ = v___x_1177_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_size_x27_1195_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_val_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
else
{
lean_object* v___x_1209_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v_buckets_x27_1197_);
lean_ctor_set(v___x_1177_, 0, v_size_x27_1195_);
v___x_1209_ = v___x_1177_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_size_x27_1195_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_buckets_x27_1197_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
else
{
lean_object* v___x_1211_; lean_object* v_buckets_x27_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1216_; 
lean_inc(v_bkt_1192_);
v___x_1211_ = lean_box(0);
v_buckets_x27_1212_ = lean_array_uset(v_buckets_1175_, v___x_1191_, v___x_1211_);
v___x_1213_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(v_a_1172_, v_b_1173_, v_bkt_1192_);
v___x_1214_ = lean_array_uset(v_buckets_x27_1212_, v___x_1191_, v___x_1213_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v___x_1214_);
v___x_1216_ = v___x_1177_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_size_1174_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1(lean_object* v_a_1219_, lean_object* v_e_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1223_ = lean_st_ref_take(v_a_1219_);
v___x_1224_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(v___x_1223_, v_e_1220_, v_a_1221_);
v___x_1225_ = lean_st_ref_set(v_a_1219_, v___x_1224_);
v___x_1226_ = lean_box(0);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_a_1227_, lean_object* v_e_1228_, lean_object* v_a_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1(v_a_1227_, v_e_1228_, v_a_1229_);
lean_dec(v_a_1227_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(lean_object* v_name_1232_, lean_object* v_type_1233_, lean_object* v_val_1234_, lean_object* v_k_1235_, uint8_t v_nondep_1236_, uint8_t v_kind_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___f_1244_; lean_object* v___x_1245_; 
lean_inc(v___y_1238_);
v___f_1244_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1244_, 0, v_k_1235_);
lean_closure_set(v___f_1244_, 1, v___y_1238_);
v___x_1245_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1232_, v_type_1233_, v_val_1234_, v___f_1244_, v_nondep_1236_, v_kind_1237_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
if (lean_obj_tag(v___x_1245_) == 0)
{
return v___x_1245_;
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1245_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg___boxed(lean_object* v_name_1254_, lean_object* v_type_1255_, lean_object* v_val_1256_, lean_object* v_k_1257_, lean_object* v_nondep_1258_, lean_object* v_kind_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
uint8_t v_nondep_boxed_1266_; uint8_t v_kind_boxed_1267_; lean_object* v_res_1268_; 
v_nondep_boxed_1266_ = lean_unbox(v_nondep_1258_);
v_kind_boxed_1267_ = lean_unbox(v_kind_1259_);
v_res_1268_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(v_name_1254_, v_type_1255_, v_val_1256_, v_k_1257_, v_nondep_boxed_1266_, v_kind_boxed_1267_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0___boxed(lean_object* v_fvars_1269_, lean_object* v_f_1270_, lean_object* v_body_1271_, lean_object* v_x_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0(v_fvars_1269_, v_f_1270_, v_body_1271_, v_x_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(lean_object* v_f_1280_, lean_object* v_fvars_1281_, lean_object* v_a_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
if (lean_obj_tag(v_a_1282_) == 8)
{
lean_object* v_declName_1289_; lean_object* v_type_1290_; lean_object* v_value_1291_; lean_object* v_body_1292_; lean_object* v_d_1293_; lean_object* v___x_1294_; 
v_declName_1289_ = lean_ctor_get(v_a_1282_, 0);
lean_inc(v_declName_1289_);
v_type_1290_ = lean_ctor_get(v_a_1282_, 1);
lean_inc_ref(v_type_1290_);
v_value_1291_ = lean_ctor_get(v_a_1282_, 2);
lean_inc_ref(v_value_1291_);
v_body_1292_ = lean_ctor_get(v_a_1282_, 3);
lean_inc_ref(v_body_1292_);
lean_dec_ref(v_a_1282_);
v_d_1293_ = lean_expr_instantiate_rev(v_type_1290_, v_fvars_1281_);
lean_dec_ref(v_type_1290_);
lean_inc_ref(v_f_1280_);
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
lean_inc(v___y_1285_);
lean_inc_ref(v___y_1284_);
lean_inc(v___y_1283_);
lean_inc_ref(v_d_1293_);
v___x_1294_ = lean_apply_7(v_f_1280_, v_d_1293_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, lean_box(0));
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_v_1295_; lean_object* v___x_1296_; 
lean_dec_ref(v___x_1294_);
v_v_1295_ = lean_expr_instantiate_rev(v_value_1291_, v_fvars_1281_);
lean_dec_ref(v_value_1291_);
lean_inc_ref(v_f_1280_);
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
lean_inc(v___y_1285_);
lean_inc_ref(v___y_1284_);
lean_inc(v___y_1283_);
lean_inc_ref(v_v_1295_);
v___x_1296_ = lean_apply_7(v_f_1280_, v_v_1295_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, lean_box(0));
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v___f_1297_; uint8_t v___x_1298_; uint8_t v___x_1299_; lean_object* v___x_1300_; 
lean_dec_ref(v___x_1296_);
v___f_1297_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1297_, 0, v_fvars_1281_);
lean_closure_set(v___f_1297_, 1, v_f_1280_);
lean_closure_set(v___f_1297_, 2, v_body_1292_);
v___x_1298_ = 0;
v___x_1299_ = 0;
v___x_1300_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(v_declName_1289_, v_d_1293_, v_v_1295_, v___f_1297_, v___x_1298_, v___x_1299_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
return v___x_1300_;
}
else
{
lean_dec_ref(v_v_1295_);
lean_dec_ref(v_d_1293_);
lean_dec_ref(v_body_1292_);
lean_dec(v_declName_1289_);
lean_dec_ref(v_fvars_1281_);
lean_dec_ref(v_f_1280_);
return v___x_1296_;
}
}
else
{
lean_dec_ref(v_d_1293_);
lean_dec_ref(v_body_1292_);
lean_dec_ref(v_value_1291_);
lean_dec(v_declName_1289_);
lean_dec_ref(v_fvars_1281_);
lean_dec_ref(v_f_1280_);
return v___x_1294_;
}
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = lean_expr_instantiate_rev(v_a_1282_, v_fvars_1281_);
lean_dec_ref(v_fvars_1281_);
lean_dec_ref(v_a_1282_);
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
lean_inc(v___y_1285_);
lean_inc_ref(v___y_1284_);
lean_inc(v___y_1283_);
v___x_1302_ = lean_apply_7(v_f_1280_, v___x_1301_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, lean_box(0));
return v___x_1302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0(lean_object* v_fvars_1303_, lean_object* v_f_1304_, lean_object* v_body_1305_, lean_object* v_x_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = lean_array_push(v_fvars_1303_, v_x_1306_);
v___x_1314_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(v_f_1304_, v___x_1313_, v_body_1305_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___boxed(lean_object* v_f_1315_, lean_object* v_fvars_1316_, lean_object* v_a_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(v_f_1315_, v_fvars_1316_, v_a_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(lean_object* v_f_1325_, lean_object* v_e_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_1334_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(v_f_1325_, v___x_1333_, v_e_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11___boxed(lean_object* v_f_1335_, lean_object* v_e_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(v_f_1335_, v_e_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed(lean_object* v_fn_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2(v_fn_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(lean_object* v_fn_1353_, lean_object* v_e_1354_, lean_object* v_a_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_a_1362_; lean_object* v___y_1374_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_inc(v_a_1355_);
v___x_1376_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1376_, 0, lean_box(0));
lean_closure_set(v___x_1376_, 1, lean_box(0));
lean_closure_set(v___x_1376_, 2, v_a_1355_);
v___x_1377_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_box(0), v___x_1376_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1414_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1414_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1414_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_a_1378_, v_e_1354_);
lean_dec(v_a_1378_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v___x_1383_; 
lean_del_object(v___x_1380_);
lean_inc_ref(v_fn_1353_);
lean_inc(v___y_1359_);
lean_inc_ref(v___y_1358_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc_ref(v_e_1354_);
v___x_1383_ = lean_apply_6(v_fn_1353_, v_e_1354_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, lean_box(0));
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; uint8_t v___x_1385_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref(v___x_1383_);
v___x_1385_ = lean_unbox(v_a_1384_);
lean_dec(v_a_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; 
lean_dec_ref(v_fn_1353_);
v___x_1386_ = lean_box(0);
v_a_1362_ = v___x_1386_;
goto v___jp_1361_;
}
else
{
switch(lean_obj_tag(v_e_1354_))
{
case 7:
{
lean_object* v___f_1387_; lean_object* v___x_1388_; 
v___f_1387_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1387_, 0, v_fn_1353_);
lean_inc_ref(v_e_1354_);
v___x_1388_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(v___f_1387_, v_e_1354_, v_a_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
v___y_1374_ = v___x_1388_;
goto v___jp_1373_;
}
case 6:
{
lean_object* v___f_1389_; lean_object* v___x_1390_; 
v___f_1389_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1389_, 0, v_fn_1353_);
lean_inc_ref(v_e_1354_);
v___x_1390_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(v___f_1389_, v_e_1354_, v_a_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
v___y_1374_ = v___x_1390_;
goto v___jp_1373_;
}
case 8:
{
lean_object* v___f_1391_; lean_object* v___x_1392_; 
v___f_1391_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1391_, 0, v_fn_1353_);
lean_inc_ref(v_e_1354_);
v___x_1392_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(v___f_1391_, v_e_1354_, v_a_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
v___y_1374_ = v___x_1392_;
goto v___jp_1373_;
}
case 5:
{
lean_object* v_fn_1393_; lean_object* v_arg_1394_; lean_object* v___x_1395_; 
v_fn_1393_ = lean_ctor_get(v_e_1354_, 0);
v_arg_1394_ = lean_ctor_get(v_e_1354_, 1);
lean_inc_ref(v_fn_1393_);
lean_inc_ref(v_fn_1353_);
v___x_1395_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1353_, v_fn_1393_, v_a_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v___x_1396_; 
lean_dec_ref(v___x_1395_);
lean_inc_ref(v_arg_1394_);
v___x_1396_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1353_, v_arg_1394_, v_a_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
v___y_1374_ = v___x_1396_;
goto v___jp_1373_;
}
else
{
lean_dec_ref(v_fn_1353_);
v___y_1374_ = v___x_1395_;
goto v___jp_1373_;
}
}
case 10:
{
lean_object* v_expr_1397_; lean_object* v___x_1398_; 
v_expr_1397_ = lean_ctor_get(v_e_1354_, 1);
lean_inc_ref(v_expr_1397_);
v___x_1398_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1353_, v_expr_1397_, v_a_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
v___y_1374_ = v___x_1398_;
goto v___jp_1373_;
}
case 11:
{
lean_object* v_struct_1399_; lean_object* v___x_1400_; 
v_struct_1399_ = lean_ctor_get(v_e_1354_, 2);
lean_inc_ref(v_struct_1399_);
v___x_1400_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1353_, v_struct_1399_, v_a_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
v___y_1374_ = v___x_1400_;
goto v___jp_1373_;
}
default: 
{
lean_object* v___x_1401_; 
lean_dec_ref(v_fn_1353_);
v___x_1401_ = lean_box(0);
v_a_1362_ = v___x_1401_;
goto v___jp_1361_;
}
}
}
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_dec_ref(v_e_1354_);
lean_dec_ref(v_fn_1353_);
v_a_1402_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1383_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1383_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
else
{
lean_object* v_val_1410_; lean_object* v___x_1412_; 
lean_dec_ref(v_e_1354_);
lean_dec_ref(v_fn_1353_);
v_val_1410_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_val_1410_);
lean_dec_ref(v___x_1382_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v_val_1410_);
v___x_1412_ = v___x_1380_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_val_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec_ref(v_e_1354_);
lean_dec_ref(v_fn_1353_);
v_a_1415_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1377_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1377_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
v___jp_1361_:
{
lean_object* v___f_1363_; lean_object* v___x_1364_; 
lean_inc(v_a_1355_);
v___f_1363_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1363_, 0, v_a_1355_);
lean_closure_set(v___f_1363_, 1, v_e_1354_);
lean_closure_set(v___f_1363_, 2, v_a_1362_);
v___x_1364_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_box(0), v___f_1363_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; 
v_unused_1372_ = lean_ctor_get(v___x_1364_, 0);
lean_dec(v_unused_1372_);
v___x_1366_ = v___x_1364_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_dec(v___x_1364_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v_a_1362_);
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1362_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
else
{
return v___x_1364_;
}
}
v___jp_1373_:
{
if (lean_obj_tag(v___y_1374_) == 0)
{
lean_object* v_a_1375_; 
v_a_1375_ = lean_ctor_get(v___y_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref(v___y_1374_);
v_a_1362_ = v_a_1375_;
goto v___jp_1361_;
}
else
{
lean_dec_ref(v_e_1354_);
return v___y_1374_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2(lean_object* v_fn_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___boxed(lean_object* v_fn_1432_, lean_object* v_e_1433_, lean_object* v_a_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1432_, v_e_1433_, v_a_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v_a_1434_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_object* v_00_u03b1_1441_, lean_object* v_x_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_apply_1(v_x_1442_, lean_box(0));
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0___boxed(lean_object* v_00_u03b1_1450_, lean_object* v_x_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(v_00_u03b1_1450_, v_x_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(lean_object* v_input_1458_, lean_object* v_fn_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v_a_1467_; lean_object* v___x_1468_; 
v___x_1465_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___redArg___closed__2, &l_Lean_Meta_forEachExpr_x27___redArg___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__2);
v___x_1466_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_box(0), v___x_1465_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref(v___x_1466_);
v___x_1468_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1459_, v_input_1458_, v_a_1467_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref(v___x_1468_);
v___x_1470_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1470_, 0, lean_box(0));
lean_closure_set(v___x_1470_, 1, lean_box(0));
lean_closure_set(v___x_1470_, 2, v_a_1467_);
v___x_1471_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_box(0), v___x_1470_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1478_ == 0)
{
lean_object* v_unused_1479_; 
v_unused_1479_ = lean_ctor_get(v___x_1471_, 0);
lean_dec(v_unused_1479_);
v___x_1473_ = v___x_1471_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_dec(v___x_1471_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v_a_1469_);
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1469_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
else
{
lean_dec(v_a_1467_);
return v___x_1468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___boxed(lean_object* v_input_1480_, lean_object* v_fn_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(v_input_1480_, v_fn_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0(lean_object* v_f_1488_, lean_object* v_e_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v___x_1495_; 
lean_inc(v___y_1493_);
lean_inc_ref(v___y_1492_);
lean_inc(v___y_1491_);
lean_inc_ref(v___y_1490_);
v___x_1495_ = lean_apply_6(v_f_1488_, v_e_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, lean_box(0));
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1504_; 
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1504_ == 0)
{
lean_object* v_unused_1505_; 
v_unused_1505_ = lean_ctor_get(v___x_1495_, 0);
lean_dec(v_unused_1505_);
v___x_1497_ = v___x_1495_;
v_isShared_1498_ = v_isSharedCheck_1504_;
goto v_resetjp_1496_;
}
else
{
lean_dec(v___x_1495_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1504_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
uint8_t v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1499_ = 1;
v___x_1500_ = lean_box(v___x_1499_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1500_);
v___x_1502_ = v___x_1497_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
v_a_1506_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1495_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1495_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0___boxed(lean_object* v_f_1514_, lean_object* v_e_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0(v_f_1514_, v_e_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(lean_object* v_e_1522_, lean_object* v_f_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v___f_1529_; lean_object* v___x_1530_; 
v___f_1529_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1529_, 0, v_f_1523_);
v___x_1530_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(v_e_1522_, v___f_1529_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___boxed(lean_object* v_e_1531_, lean_object* v_f_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(v_e_1531_, v_f_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt(lean_object* v_e_1541_, lean_object* v_isTarget_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v_a_1552_; lean_object* v___f_1553_; lean_object* v___x_1554_; 
v___x_1548_ = lean_unsigned_to_nat(0u);
v___x_1549_ = ((lean_object*)(l_Lean_Meta_setMVarUserNamesAt___closed__0));
v___x_1550_ = lean_st_mk_ref(v___x_1549_);
v___x_1551_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(v_e_1541_, v_a_1544_);
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref(v___x_1551_);
lean_inc(v___x_1550_);
v___f_1553_ = lean_alloc_closure((void*)(l_Lean_Meta_setMVarUserNamesAt___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1553_, 0, v___x_1550_);
lean_closure_set(v___f_1553_, 1, v_isTarget_1542_);
lean_closure_set(v___f_1553_, 2, v___x_1548_);
v___x_1554_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(v_a_1552_, v___f_1553_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1562_; 
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1562_ == 0)
{
lean_object* v_unused_1563_; 
v_unused_1563_ = lean_ctor_get(v___x_1554_, 0);
lean_dec(v_unused_1563_);
v___x_1556_ = v___x_1554_;
v_isShared_1557_ = v_isSharedCheck_1562_;
goto v_resetjp_1555_;
}
else
{
lean_dec(v___x_1554_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1562_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1558_ = lean_st_ref_get(v___x_1550_);
lean_dec(v___x_1550_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1558_);
v___x_1560_ = v___x_1556_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec(v___x_1550_);
v_a_1564_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1554_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1554_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___boxed(lean_object* v_e_1572_, lean_object* v_isTarget_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_Meta_setMVarUserNamesAt(v_e_1572_, v_isTarget_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2(lean_object* v_upperBound_1580_, lean_object* v___x_1581_, lean_object* v_val_1582_, lean_object* v_e_1583_, lean_object* v_isTarget_1584_, lean_object* v_inst_1585_, lean_object* v_R_1586_, lean_object* v_a_1587_, lean_object* v_b_1588_, lean_object* v_c_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(v_upperBound_1580_, v___x_1581_, v_val_1582_, v_e_1583_, v_isTarget_1584_, v_a_1587_, v_b_1588_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___boxed(lean_object* v_upperBound_1596_, lean_object* v___x_1597_, lean_object* v_val_1598_, lean_object* v_e_1599_, lean_object* v_isTarget_1600_, lean_object* v_inst_1601_, lean_object* v_R_1602_, lean_object* v_a_1603_, lean_object* v_b_1604_, lean_object* v_c_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2(v_upperBound_1596_, v___x_1597_, v_val_1598_, v_e_1599_, v_isTarget_1600_, v_inst_1601_, v_R_1602_, v_a_1603_, v_b_1604_, v_c_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec_ref(v_isTarget_1600_);
lean_dec_ref(v_e_1599_);
lean_dec_ref(v___x_1597_);
lean_dec(v_upperBound_1596_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_1612_, lean_object* v_m_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_m_1613_, v_a_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___boxed(lean_object* v_00_u03b2_1616_, lean_object* v_m_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7(v_00_u03b2_1616_, v_m_1617_, v_a_1618_);
lean_dec_ref(v_a_1618_);
lean_dec_ref(v_m_1617_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_1620_, lean_object* v_m_1621_, lean_object* v_a_1622_, lean_object* v_b_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(v_m_1621_, v_a_1622_, v_b_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_1625_, lean_object* v_a_1626_, lean_object* v_x_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(v_a_1626_, v_x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03b2_1629_, lean_object* v_a_1630_, lean_object* v_x_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8(v_00_u03b2_1629_, v_a_1630_, v_x_1631_);
lean_dec(v_x_1631_);
lean_dec_ref(v_a_1630_);
return v_res_1632_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_1633_, lean_object* v_a_1634_, lean_object* v_x_1635_){
_start:
{
uint8_t v___x_1636_; 
v___x_1636_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_a_1634_, v_x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b2_1637_, lean_object* v_a_1638_, lean_object* v_x_1639_){
_start:
{
uint8_t v_res_1640_; lean_object* v_r_1641_; 
v_res_1640_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10(v_00_u03b2_1637_, v_a_1638_, v_x_1639_);
lean_dec(v_x_1639_);
lean_dec_ref(v_a_1638_);
v_r_1641_ = lean_box(v_res_1640_);
return v_r_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11(lean_object* v_00_u03b2_1642_, lean_object* v_data_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11___redArg(v_data_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12(lean_object* v_00_u03b2_1645_, lean_object* v_a_1646_, lean_object* v_b_1647_, lean_object* v_x_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(v_a_1646_, v_b_1647_, v_x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16(lean_object* v_00_u03b1_1650_, lean_object* v_name_1651_, uint8_t v_bi_1652_, lean_object* v_type_1653_, lean_object* v_k_1654_, uint8_t v_kind_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_name_1651_, v_bi_1652_, v_type_1653_, v_k_1654_, v_kind_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1663_, lean_object* v_name_1664_, lean_object* v_bi_1665_, lean_object* v_type_1666_, lean_object* v_k_1667_, lean_object* v_kind_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
uint8_t v_bi_boxed_1675_; uint8_t v_kind_boxed_1676_; lean_object* v_res_1677_; 
v_bi_boxed_1675_ = lean_unbox(v_bi_1665_);
v_kind_boxed_1676_ = lean_unbox(v_kind_1668_);
v_res_1677_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16(v_00_u03b1_1663_, v_name_1664_, v_bi_boxed_1675_, v_type_1666_, v_k_1667_, v_kind_boxed_1676_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21(lean_object* v_00_u03b1_1678_, lean_object* v_name_1679_, lean_object* v_type_1680_, lean_object* v_val_1681_, lean_object* v_k_1682_, uint8_t v_nondep_1683_, uint8_t v_kind_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(v_name_1679_, v_type_1680_, v_val_1681_, v_k_1682_, v_nondep_1683_, v_kind_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___boxed(lean_object* v_00_u03b1_1692_, lean_object* v_name_1693_, lean_object* v_type_1694_, lean_object* v_val_1695_, lean_object* v_k_1696_, lean_object* v_nondep_1697_, lean_object* v_kind_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
uint8_t v_nondep_boxed_1705_; uint8_t v_kind_boxed_1706_; lean_object* v_res_1707_; 
v_nondep_boxed_1705_ = lean_unbox(v_nondep_1697_);
v_kind_boxed_1706_ = lean_unbox(v_kind_1698_);
v_res_1707_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21(v_00_u03b1_1692_, v_name_1693_, v_type_1694_, v_val_1695_, v_k_1696_, v_nondep_boxed_1705_, v_kind_boxed_1706_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_1708_, lean_object* v_i_1709_, lean_object* v_source_1710_, lean_object* v_target_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12___redArg(v_i_1709_, v_source_1710_, v_target_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16(lean_object* v_00_u03b2_1713_, lean_object* v_x_1714_, lean_object* v_x_1715_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16___redArg(v_x_1714_, v_x_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(lean_object* v_as_1717_, size_t v_sz_1718_, size_t v_i_1719_, lean_object* v_b_1720_, lean_object* v___y_1721_){
_start:
{
uint8_t v___x_1723_; 
v___x_1723_ = lean_usize_dec_lt(v_i_1719_, v_sz_1718_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; 
v___x_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1724_, 0, v_b_1720_);
return v___x_1724_;
}
else
{
lean_object* v___x_1725_; lean_object* v_mctx_1726_; lean_object* v_cache_1727_; lean_object* v_zetaDeltaFVarIds_1728_; lean_object* v_postponed_1729_; lean_object* v_diag_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1745_; 
v___x_1725_ = lean_st_ref_take(v___y_1721_);
v_mctx_1726_ = lean_ctor_get(v___x_1725_, 0);
v_cache_1727_ = lean_ctor_get(v___x_1725_, 1);
v_zetaDeltaFVarIds_1728_ = lean_ctor_get(v___x_1725_, 2);
v_postponed_1729_ = lean_ctor_get(v___x_1725_, 3);
v_diag_1730_ = lean_ctor_get(v___x_1725_, 4);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1732_ = v___x_1725_;
v_isShared_1733_ = v_isSharedCheck_1745_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_diag_1730_);
lean_inc(v_postponed_1729_);
lean_inc(v_zetaDeltaFVarIds_1728_);
lean_inc(v_cache_1727_);
lean_inc(v_mctx_1726_);
lean_dec(v___x_1725_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1745_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v_a_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1738_; 
v_a_1734_ = lean_array_uget_borrowed(v_as_1717_, v_i_1719_);
v___x_1735_ = lean_box(0);
lean_inc(v_a_1734_);
v___x_1736_ = l_Lean_MetavarContext_setMVarUserNameTemporarily(v_mctx_1726_, v_a_1734_, v___x_1735_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v___x_1736_);
v___x_1738_ = v___x_1732_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_cache_1727_);
lean_ctor_set(v_reuseFailAlloc_1744_, 2, v_zetaDeltaFVarIds_1728_);
lean_ctor_set(v_reuseFailAlloc_1744_, 3, v_postponed_1729_);
lean_ctor_set(v_reuseFailAlloc_1744_, 4, v_diag_1730_);
v___x_1738_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; size_t v___x_1741_; size_t v___x_1742_; 
v___x_1739_ = lean_st_ref_set(v___y_1721_, v___x_1738_);
v___x_1740_ = lean_box(0);
v___x_1741_ = ((size_t)1ULL);
v___x_1742_ = lean_usize_add(v_i_1719_, v___x_1741_);
v_i_1719_ = v___x_1742_;
v_b_1720_ = v___x_1740_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg___boxed(lean_object* v_as_1746_, lean_object* v_sz_1747_, lean_object* v_i_1748_, lean_object* v_b_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
size_t v_sz_boxed_1752_; size_t v_i_boxed_1753_; lean_object* v_res_1754_; 
v_sz_boxed_1752_ = lean_unbox_usize(v_sz_1747_);
lean_dec(v_sz_1747_);
v_i_boxed_1753_ = lean_unbox_usize(v_i_1748_);
lean_dec(v_i_1748_);
v_res_1754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_as_1746_, v_sz_boxed_1752_, v_i_boxed_1753_, v_b_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v_as_1746_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_resetMVarUserNames(lean_object* v_toReset_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v___x_1761_; size_t v_sz_1762_; size_t v___x_1763_; lean_object* v___x_1764_; 
v___x_1761_ = lean_box(0);
v_sz_1762_ = lean_array_size(v_toReset_1755_);
v___x_1763_ = ((size_t)0ULL);
v___x_1764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_toReset_1755_, v_sz_1762_, v___x_1763_, v___x_1761_, v_a_1757_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1771_ == 0)
{
lean_object* v_unused_1772_; 
v_unused_1772_ = lean_ctor_get(v___x_1764_, 0);
lean_dec(v_unused_1772_);
v___x_1766_ = v___x_1764_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_dec(v___x_1764_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v___x_1761_);
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1761_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
else
{
return v___x_1764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_resetMVarUserNames___boxed(lean_object* v_toReset_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lean_Meta_resetMVarUserNames(v_toReset_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
lean_dec_ref(v_toReset_1773_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0(lean_object* v_as_1780_, size_t v_sz_1781_, size_t v_i_1782_, lean_object* v_b_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_as_1780_, v_sz_1781_, v_i_1782_, v_b_1783_, v___y_1785_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___boxed(lean_object* v_as_1790_, lean_object* v_sz_1791_, lean_object* v_i_1792_, lean_object* v_b_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
size_t v_sz_boxed_1799_; size_t v_i_boxed_1800_; lean_object* v_res_1801_; 
v_sz_boxed_1799_ = lean_unbox_usize(v_sz_1791_);
lean_dec(v_sz_1791_);
v_i_boxed_1800_ = lean_unbox_usize(v_i_1792_);
lean_dec(v_i_1792_);
v_res_1801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0(v_as_1790_, v_sz_boxed_1799_, v_i_boxed_1800_, v_b_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec_ref(v_as_1790_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(lean_object* v_x_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
if (lean_obj_tag(v_x_1802_) == 2)
{
lean_object* v_mvarId_1808_; lean_object* v___x_1809_; 
v_mvarId_1808_ = lean_ctor_get(v_x_1802_, 0);
lean_inc(v_mvarId_1808_);
lean_dec_ref(v_x_1802_);
v___x_1809_ = l_Lean_MVarId_getDecl(v_mvarId_1808_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1820_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1820_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1820_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v_userName_1814_; uint8_t v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
v_userName_1814_ = lean_ctor_get(v_a_1810_, 0);
lean_inc(v_userName_1814_);
lean_dec(v_a_1810_);
v___x_1815_ = l_Lean_Name_isAnonymous(v_userName_1814_);
lean_dec(v_userName_1814_);
v___x_1816_ = lean_box(v___x_1815_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1816_);
v___x_1818_ = v___x_1812_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
v_a_1821_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1809_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1809_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
else
{
uint8_t v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_dec_ref(v_x_1802_);
v___x_1829_ = 0;
v___x_1830_ = lean_box(v___x_1829_);
v___x_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1830_);
return v___x_1831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0___boxed(lean_object* v_x_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(v_x_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__0(lean_object* v_val_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_x3f_1844_){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = lean_st_ref_get(v_val_1839_);
v___x_1847_ = l_Lean_Meta_resetMVarUserNames(v___x_1846_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
lean_dec(v___x_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__0___boxed(lean_object* v_val_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_x3f_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_Meta_mkForallFVars_x27___lam__0(v_val_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_x3f_1853_);
lean_dec(v_a_x3f_1853_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
lean_dec(v_a_1850_);
lean_dec_ref(v_a_1849_);
lean_dec(v_val_1848_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(lean_object* v_xs_1856_, lean_object* v_as_1857_, size_t v_sz_1858_, size_t v_i_1859_, lean_object* v_b_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
uint8_t v___x_1867_; 
v___x_1867_ = lean_usize_dec_lt(v_i_1859_, v_sz_1858_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; 
lean_dec_ref(v_xs_1856_);
v___x_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1868_, 0, v_b_1860_);
return v___x_1868_;
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1870_; 
v_a_1869_ = lean_array_uget_borrowed(v_as_1857_, v_i_1859_);
lean_inc(v___y_1865_);
lean_inc_ref(v___y_1864_);
lean_inc(v___y_1863_);
lean_inc_ref(v___y_1862_);
lean_inc(v_a_1869_);
v___x_1870_ = lean_infer_type(v_a_1869_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1872_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref(v___x_1870_);
lean_inc_ref(v_xs_1856_);
v___x_1872_ = l_Lean_Meta_setMVarUserNamesAt(v_a_1871_, v_xs_1856_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; size_t v___x_1878_; size_t v___x_1879_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref(v___x_1872_);
v___x_1874_ = lean_st_ref_take(v___y_1861_);
v___x_1875_ = l_Array_append___redArg(v___x_1874_, v_a_1873_);
lean_dec(v_a_1873_);
v___x_1876_ = lean_st_ref_set(v___y_1861_, v___x_1875_);
v___x_1877_ = lean_box(0);
v___x_1878_ = ((size_t)1ULL);
v___x_1879_ = lean_usize_add(v_i_1859_, v___x_1878_);
v_i_1859_ = v___x_1879_;
v_b_1860_ = v___x_1877_;
goto _start;
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec_ref(v_xs_1856_);
v_a_1881_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1872_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1872_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_dec_ref(v_xs_1856_);
v_a_1889_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1870_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1870_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2___boxed(lean_object* v_xs_1897_, lean_object* v_as_1898_, lean_object* v_sz_1899_, lean_object* v_i_1900_, lean_object* v_b_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
size_t v_sz_boxed_1908_; size_t v_i_boxed_1909_; lean_object* v_res_1910_; 
v_sz_boxed_1908_ = lean_unbox_usize(v_sz_1899_);
lean_dec(v_sz_1899_);
v_i_boxed_1909_ = lean_unbox_usize(v_i_1900_);
lean_dec(v_i_1900_);
v_res_1910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(v_xs_1897_, v_as_1898_, v_sz_boxed_1908_, v_i_boxed_1909_, v_b_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v_as_1898_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(lean_object* v_xs_1911_, lean_object* v_as_1912_, size_t v_sz_1913_, size_t v_i_1914_, lean_object* v_b_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
uint8_t v___x_1922_; 
v___x_1922_ = lean_usize_dec_lt(v_i_1914_, v_sz_1913_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; 
lean_dec_ref(v_xs_1911_);
v___x_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1923_, 0, v_b_1915_);
return v___x_1923_;
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1925_; 
v_a_1924_ = lean_array_uget_borrowed(v_as_1912_, v_i_1914_);
lean_inc(v___y_1920_);
lean_inc_ref(v___y_1919_);
lean_inc(v___y_1918_);
lean_inc_ref(v___y_1917_);
lean_inc(v_a_1924_);
v___x_1925_ = lean_infer_type(v_a_1924_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref(v___x_1925_);
lean_inc_ref(v_xs_1911_);
v___x_1927_ = l_Lean_Meta_setMVarUserNamesAt(v_a_1926_, v_xs_1911_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; size_t v___x_1933_; size_t v___x_1934_; lean_object* v___x_1935_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref(v___x_1927_);
v___x_1929_ = lean_st_ref_take(v___y_1916_);
v___x_1930_ = l_Array_append___redArg(v___x_1929_, v_a_1928_);
lean_dec(v_a_1928_);
v___x_1931_ = lean_st_ref_set(v___y_1916_, v___x_1930_);
v___x_1932_ = lean_box(0);
v___x_1933_ = ((size_t)1ULL);
v___x_1934_ = lean_usize_add(v_i_1914_, v___x_1933_);
v___x_1935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(v_xs_1911_, v_as_1912_, v_sz_1913_, v___x_1934_, v___x_1932_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
return v___x_1935_;
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec_ref(v_xs_1911_);
v_a_1936_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1927_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1927_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec_ref(v_xs_1911_);
v_a_1944_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1925_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1925_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2___boxed(lean_object* v_xs_1952_, lean_object* v_as_1953_, lean_object* v_sz_1954_, lean_object* v_i_1955_, lean_object* v_b_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
size_t v_sz_boxed_1963_; size_t v_i_boxed_1964_; lean_object* v_res_1965_; 
v_sz_boxed_1963_ = lean_unbox_usize(v_sz_1954_);
lean_dec(v_sz_1954_);
v_i_boxed_1964_ = lean_unbox_usize(v_i_1955_);
lean_dec(v_i_1955_);
v_res_1965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(v_xs_1952_, v_as_1953_, v_sz_boxed_1963_, v_i_boxed_1964_, v_b_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v_as_1953_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(lean_object* v_as_1966_, size_t v_i_1967_, size_t v_stop_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
uint8_t v___x_1974_; 
v___x_1974_ = lean_usize_dec_eq(v_i_1967_, v_stop_1968_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = lean_array_uget_borrowed(v_as_1966_, v_i_1967_);
lean_inc(v___x_1975_);
v___x_1976_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(v___x_1975_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1988_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1979_ = v___x_1976_;
v_isShared_1980_ = v_isSharedCheck_1988_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1976_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1988_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
uint8_t v___x_1981_; 
v___x_1981_ = lean_unbox(v_a_1977_);
if (v___x_1981_ == 0)
{
size_t v___x_1982_; size_t v___x_1983_; 
lean_del_object(v___x_1979_);
lean_dec(v_a_1977_);
v___x_1982_ = ((size_t)1ULL);
v___x_1983_ = lean_usize_add(v_i_1967_, v___x_1982_);
v_i_1967_ = v___x_1983_;
goto _start;
}
else
{
lean_object* v___x_1986_; 
if (v_isShared_1980_ == 0)
{
v___x_1986_ = v___x_1979_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1977_);
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
return v___x_1976_;
}
}
else
{
uint8_t v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = 0;
v___x_1990_ = lean_box(v___x_1989_);
v___x_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
return v___x_1991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1___boxed(lean_object* v_as_1992_, lean_object* v_i_1993_, lean_object* v_stop_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
size_t v_i_boxed_2000_; size_t v_stop_boxed_2001_; lean_object* v_res_2002_; 
v_i_boxed_2000_ = lean_unbox_usize(v_i_1993_);
lean_dec(v_i_1993_);
v_stop_boxed_2001_ = lean_unbox_usize(v_stop_1994_);
lean_dec(v_stop_1994_);
v_res_2002_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(v_as_1992_, v_i_boxed_2000_, v_stop_boxed_2001_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec_ref(v_as_1992_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27(lean_object* v_xs_2003_, lean_object* v_type_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
uint8_t v_a_2011_; lean_object* v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2015_ = lean_unsigned_to_nat(0u);
v___x_2016_ = lean_array_get_size(v_xs_2003_);
v___x_2017_ = lean_nat_dec_lt(v___x_2015_, v___x_2016_);
if (v___x_2017_ == 0)
{
v_a_2011_ = v___x_2017_;
goto v___jp_2010_;
}
else
{
if (v___x_2017_ == 0)
{
v_a_2011_ = v___x_2017_;
goto v___jp_2010_;
}
else
{
size_t v___x_2018_; size_t v___x_2019_; lean_object* v___x_2020_; 
v___x_2018_ = ((size_t)0ULL);
v___x_2019_ = lean_usize_of_nat(v___x_2016_);
v___x_2020_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(v_xs_2003_, v___x_2018_, v___x_2019_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; uint8_t v___x_2022_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref(v___x_2020_);
v___x_2022_ = lean_unbox(v_a_2021_);
if (v___x_2022_ == 0)
{
uint8_t v___x_2023_; 
v___x_2023_ = lean_unbox(v_a_2021_);
lean_dec(v_a_2021_);
v_a_2011_ = v___x_2023_;
goto v___jp_2010_;
}
else
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v_a_2027_; lean_object* v___x_2046_; size_t v_sz_2047_; lean_object* v___x_2048_; 
lean_dec(v_a_2021_);
v___x_2024_ = ((lean_object*)(l_Lean_Meta_setMVarUserNamesAt___closed__0));
v___x_2025_ = lean_st_mk_ref(v___x_2024_);
v___x_2046_ = lean_box(0);
v_sz_2047_ = lean_array_size(v_xs_2003_);
lean_inc_ref(v_xs_2003_);
v___x_2048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(v_xs_2003_, v_xs_2003_, v_sz_2047_, v___x_2018_, v___x_2046_, v___x_2025_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v___x_2049_; 
lean_dec_ref(v___x_2048_);
lean_inc_ref(v_xs_2003_);
lean_inc_ref(v_type_2004_);
v___x_2049_ = l_Lean_Meta_setMVarUserNamesAt(v_type_2004_, v_xs_2003_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; uint8_t v___x_2054_; uint8_t v___x_2055_; lean_object* v___x_2056_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref(v___x_2049_);
v___x_2051_ = lean_st_ref_take(v___x_2025_);
v___x_2052_ = l_Array_append___redArg(v___x_2051_, v_a_2050_);
lean_dec(v_a_2050_);
v___x_2053_ = lean_st_ref_set(v___x_2025_, v___x_2052_);
v___x_2054_ = 0;
v___x_2055_ = 1;
v___x_2056_ = l_Lean_Meta_mkForallFVars(v_xs_2003_, v_type_2004_, v___x_2054_, v___x_2017_, v___x_2017_, v___x_2055_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
lean_dec_ref(v_xs_2003_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2082_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2082_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2056_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2082_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
lean_inc(v_a_2057_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set_tag(v___x_2059_, 1);
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
lean_object* v___x_2063_; 
v___x_2063_ = l_Lean_Meta_mkForallFVars_x27___lam__0(v___x_2025_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v___x_2062_);
lean_dec_ref(v___x_2062_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2071_; 
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2071_ == 0)
{
lean_object* v_unused_2072_; 
v_unused_2072_ = lean_ctor_get(v___x_2063_, 0);
lean_dec(v_unused_2072_);
v___x_2065_ = v___x_2063_;
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
else
{
lean_dec(v___x_2063_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_st_ref_get(v___x_2025_);
lean_dec(v___x_2025_);
lean_dec(v___x_2067_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v_a_2057_);
v___x_2069_ = v___x_2065_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2057_);
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
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec(v_a_2057_);
lean_dec(v___x_2025_);
v_a_2073_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2063_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2063_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
}
else
{
lean_object* v_a_2083_; 
v_a_2083_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2083_);
lean_dec_ref(v___x_2056_);
v_a_2027_ = v_a_2083_;
goto v___jp_2026_;
}
}
else
{
lean_object* v_a_2084_; 
lean_dec_ref(v_type_2004_);
lean_dec_ref(v_xs_2003_);
v_a_2084_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2084_);
lean_dec_ref(v___x_2049_);
v_a_2027_ = v_a_2084_;
goto v___jp_2026_;
}
}
else
{
lean_object* v_a_2085_; 
lean_dec_ref(v_type_2004_);
lean_dec_ref(v_xs_2003_);
v_a_2085_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2085_);
lean_dec_ref(v___x_2048_);
v_a_2027_ = v_a_2085_;
goto v___jp_2026_;
}
v___jp_2026_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = lean_box(0);
v___x_2029_ = l_Lean_Meta_mkForallFVars_x27___lam__0(v___x_2025_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v___x_2028_);
lean_dec(v___x_2025_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; 
v_unused_2037_ = lean_ctor_get(v___x_2029_, 0);
lean_dec(v_unused_2037_);
v___x_2031_ = v___x_2029_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_dec(v___x_2029_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
lean_ctor_set_tag(v___x_2031_, 1);
lean_ctor_set(v___x_2031_, 0, v_a_2027_);
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2027_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec_ref(v_a_2027_);
v_a_2038_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2029_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2029_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec_ref(v_type_2004_);
lean_dec_ref(v_xs_2003_);
v_a_2086_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2020_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2020_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
v___jp_2010_:
{
uint8_t v___x_2012_; uint8_t v___x_2013_; lean_object* v___x_2014_; 
v___x_2012_ = 1;
v___x_2013_ = 1;
v___x_2014_ = l_Lean_Meta_mkForallFVars(v_xs_2003_, v_type_2004_, v_a_2011_, v___x_2012_, v___x_2012_, v___x_2013_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
lean_dec_ref(v_xs_2003_);
return v___x_2014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___boxed(lean_object* v_xs_2094_, lean_object* v_type_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Lean_Meta_mkForallFVars_x27(v_xs_2094_, v_type_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
return v_res_2101_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_ForEachExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
