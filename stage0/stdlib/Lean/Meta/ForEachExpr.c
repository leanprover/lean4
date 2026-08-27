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
lean_object* l_Lean_MonadCacheT_instMonadControl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v_binderInfo_62__boxed_17_; lean_object* v_res_18_; 
v_binderInfo_62__boxed_17_ = lean_unbox(v_binderInfo_13_);
v_res_18_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1(v_inst_10_, v_inst_11_, v_binderName_12_, v_binderInfo_62__boxed_17_, v_d_14_, v___f_15_, v_____r_16_);
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
lean_dec_ref_known(v_a_229_, 1);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5(lean_object* v_toApplicative_255_, lean_object* v_e_256_, lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_fn_259_, lean_object* v_x_260_, lean_object* v_x_261_, lean_object* v___x_262_, lean_object* v___x_263_, lean_object* v_a_264_, lean_object* v_toBind_265_, uint8_t v_a_266_){
_start:
{
if (v_a_266_ == 0)
{
lean_object* v_toPure_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec(v_toBind_265_);
lean_dec_ref(v___x_263_);
lean_dec_ref(v___x_262_);
lean_dec(v_x_261_);
lean_dec(v_fn_259_);
lean_dec_ref(v_inst_258_);
lean_dec_ref(v_inst_257_);
lean_dec_ref(v_e_256_);
v_toPure_267_ = lean_ctor_get(v_toApplicative_255_, 1);
lean_inc(v_toPure_267_);
lean_dec_ref(v_toApplicative_255_);
v___x_268_ = lean_box(0);
v___x_269_ = lean_apply_2(v_toPure_267_, lean_box(0), v___x_268_);
return v___x_269_;
}
else
{
switch(lean_obj_tag(v_e_256_))
{
case 7:
{
lean_object* v___x_270_; lean_object* v___x_735__overap_271_; lean_object* v___x_272_; 
lean_dec(v_toBind_265_);
lean_dec_ref(v_toApplicative_255_);
v___x_270_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed), 7, 5);
lean_closure_set(v___x_270_, 0, v_inst_257_);
lean_closure_set(v___x_270_, 1, v_inst_258_);
lean_closure_set(v___x_270_, 2, v_fn_259_);
lean_closure_set(v___x_270_, 3, v_x_260_);
lean_closure_set(v___x_270_, 4, v_x_261_);
v___x_735__overap_271_ = l_Lean_Meta_visitForall___redArg(v___x_262_, v___x_263_, v___x_270_, v_e_256_);
lean_inc(v_a_264_);
v___x_272_ = lean_apply_1(v___x_735__overap_271_, v_a_264_);
return v___x_272_;
}
case 6:
{
lean_object* v___x_273_; lean_object* v___x_741__overap_274_; lean_object* v___x_275_; 
lean_dec(v_toBind_265_);
lean_dec_ref(v_toApplicative_255_);
v___x_273_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed), 7, 5);
lean_closure_set(v___x_273_, 0, v_inst_257_);
lean_closure_set(v___x_273_, 1, v_inst_258_);
lean_closure_set(v___x_273_, 2, v_fn_259_);
lean_closure_set(v___x_273_, 3, v_x_260_);
lean_closure_set(v___x_273_, 4, v_x_261_);
v___x_741__overap_274_ = l_Lean_Meta_visitLambda___redArg(v___x_262_, v___x_263_, v___x_273_, v_e_256_);
lean_inc(v_a_264_);
v___x_275_ = lean_apply_1(v___x_741__overap_274_, v_a_264_);
return v___x_275_;
}
case 8:
{
lean_object* v___x_276_; lean_object* v___x_748__overap_277_; lean_object* v___x_278_; 
lean_dec(v_toBind_265_);
lean_dec_ref(v_toApplicative_255_);
v___x_276_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed), 7, 5);
lean_closure_set(v___x_276_, 0, v_inst_257_);
lean_closure_set(v___x_276_, 1, v_inst_258_);
lean_closure_set(v___x_276_, 2, v_fn_259_);
lean_closure_set(v___x_276_, 3, v_x_260_);
lean_closure_set(v___x_276_, 4, v_x_261_);
v___x_748__overap_277_ = l_Lean_Meta_visitLet___redArg(v___x_262_, v___x_263_, v___x_276_, v_e_256_);
lean_inc(v_a_264_);
v___x_278_ = lean_apply_1(v___x_748__overap_277_, v_a_264_);
return v___x_278_;
}
case 5:
{
lean_object* v_fn_279_; lean_object* v_arg_280_; lean_object* v___f_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec_ref(v___x_263_);
lean_dec_ref(v___x_262_);
lean_dec_ref(v_toApplicative_255_);
v_fn_279_ = lean_ctor_get(v_e_256_, 0);
lean_inc_ref(v_fn_279_);
v_arg_280_ = lean_ctor_get(v_e_256_, 1);
lean_inc_ref(v_arg_280_);
lean_dec_ref_known(v_e_256_, 2);
lean_inc(v_a_264_);
lean_inc(v_x_261_);
lean_inc(v_fn_259_);
lean_inc_ref(v_inst_258_);
lean_inc_ref(v_inst_257_);
v___f_281_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_281_, 0, v_inst_257_);
lean_closure_set(v___f_281_, 1, v_inst_258_);
lean_closure_set(v___f_281_, 2, v_fn_259_);
lean_closure_set(v___f_281_, 3, v_x_260_);
lean_closure_set(v___f_281_, 4, v_x_261_);
lean_closure_set(v___f_281_, 5, v_arg_280_);
lean_closure_set(v___f_281_, 6, v_a_264_);
v___x_282_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_257_, v_inst_258_, v_fn_259_, v_x_260_, v_x_261_, v_fn_279_, v_a_264_);
v___x_283_ = lean_apply_4(v_toBind_265_, lean_box(0), lean_box(0), v___x_282_, v___f_281_);
return v___x_283_;
}
case 10:
{
lean_object* v_expr_284_; lean_object* v___x_285_; 
lean_dec(v_toBind_265_);
lean_dec_ref(v___x_263_);
lean_dec_ref(v___x_262_);
lean_dec_ref(v_toApplicative_255_);
v_expr_284_ = lean_ctor_get(v_e_256_, 1);
lean_inc_ref(v_expr_284_);
lean_dec_ref_known(v_e_256_, 2);
v___x_285_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_257_, v_inst_258_, v_fn_259_, v_x_260_, v_x_261_, v_expr_284_, v_a_264_);
return v___x_285_;
}
case 11:
{
lean_object* v_struct_286_; lean_object* v___x_287_; 
lean_dec(v_toBind_265_);
lean_dec_ref(v___x_263_);
lean_dec_ref(v___x_262_);
lean_dec_ref(v_toApplicative_255_);
v_struct_286_ = lean_ctor_get(v_e_256_, 2);
lean_inc_ref(v_struct_286_);
lean_dec_ref_known(v_e_256_, 3);
v___x_287_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_257_, v_inst_258_, v_fn_259_, v_x_260_, v_x_261_, v_struct_286_, v_a_264_);
return v___x_287_;
}
default: 
{
lean_object* v_toPure_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec(v_toBind_265_);
lean_dec_ref(v___x_263_);
lean_dec_ref(v___x_262_);
lean_dec(v_x_261_);
lean_dec(v_fn_259_);
lean_dec_ref(v_inst_258_);
lean_dec_ref(v_inst_257_);
lean_dec_ref(v_e_256_);
v_toPure_288_ = lean_ctor_get(v_toApplicative_255_, 1);
lean_inc(v_toPure_288_);
lean_dec_ref(v_toApplicative_255_);
v___x_289_ = lean_box(0);
v___x_290_ = lean_apply_2(v_toPure_288_, lean_box(0), v___x_289_);
return v___x_290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___boxed(lean_object* v_toApplicative_291_, lean_object* v_e_292_, lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_fn_295_, lean_object* v_x_296_, lean_object* v_x_297_, lean_object* v___x_298_, lean_object* v___x_299_, lean_object* v_a_300_, lean_object* v_toBind_301_, lean_object* v_a_302_){
_start:
{
uint8_t v_a_boxed_303_; lean_object* v_res_304_; 
v_a_boxed_303_ = lean_unbox(v_a_302_);
v_res_304_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5(v_toApplicative_291_, v_e_292_, v_inst_293_, v_inst_294_, v_fn_295_, v_x_296_, v_x_297_, v___x_298_, v___x_299_, v_a_300_, v_toBind_301_, v_a_boxed_303_);
lean_dec(v_a_300_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_fn_307_, lean_object* v_x_308_, lean_object* v_x_309_, lean_object* v_e_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___f_316_; lean_object* v___f_317_; lean_object* v___x_318_; lean_object* v_toApplicative_319_; lean_object* v_toBind_320_; lean_object* v___f_321_; lean_object* v___f_322_; lean_object* v___f_323_; lean_object* v___f_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_312_ = ((lean_object*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__0));
v___x_313_ = ((lean_object*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__1));
lean_inc_ref(v_inst_305_);
v___x_314_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_308_, v___x_312_, v___x_313_, v_inst_305_);
v___x_315_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_308_, v___x_312_, v___x_313_);
lean_inc_ref_n(v_inst_306_, 2);
lean_inc_ref(v___x_315_);
v___f_316_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_316_, 0, v___x_315_);
lean_closure_set(v___f_316_, 1, v_inst_306_);
v___f_317_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_317_, 0, v___x_315_);
lean_closure_set(v___f_317_, 1, v_inst_306_);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v___f_316_);
lean_ctor_set(v___x_318_, 1, v___f_317_);
v_toApplicative_319_ = lean_ctor_get(v_inst_305_, 0);
lean_inc_ref_n(v_toApplicative_319_, 4);
v_toBind_320_ = lean_ctor_get(v_inst_305_, 1);
lean_inc_n(v_toBind_320_, 5);
lean_inc_n(v_x_309_, 2);
lean_inc_n(v_a_311_, 3);
lean_inc_ref_n(v_e_310_, 3);
v___f_321_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_321_, 0, v_toApplicative_319_);
lean_closure_set(v___f_321_, 1, v___x_312_);
lean_closure_set(v___f_321_, 2, v___x_313_);
lean_closure_set(v___f_321_, 3, v_e_310_);
lean_closure_set(v___f_321_, 4, v_a_311_);
lean_closure_set(v___f_321_, 5, v_x_309_);
lean_closure_set(v___f_321_, 6, v_toBind_320_);
v___f_322_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_322_, 0, v_toApplicative_319_);
lean_closure_set(v___f_322_, 1, v___x_312_);
lean_closure_set(v___f_322_, 2, v___x_313_);
lean_closure_set(v___f_322_, 3, v_e_310_);
lean_inc(v_fn_307_);
v___f_323_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___boxed), 12, 11);
lean_closure_set(v___f_323_, 0, v_toApplicative_319_);
lean_closure_set(v___f_323_, 1, v_e_310_);
lean_closure_set(v___f_323_, 2, v_inst_305_);
lean_closure_set(v___f_323_, 3, v_inst_306_);
lean_closure_set(v___f_323_, 4, v_fn_307_);
lean_closure_set(v___f_323_, 5, v_x_308_);
lean_closure_set(v___f_323_, 6, v_x_309_);
lean_closure_set(v___f_323_, 7, v___x_314_);
lean_closure_set(v___f_323_, 8, v___x_318_);
lean_closure_set(v___f_323_, 9, v_a_311_);
lean_closure_set(v___f_323_, 10, v_toBind_320_);
v___f_324_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__6), 7, 6);
lean_closure_set(v___f_324_, 0, v_fn_307_);
lean_closure_set(v___f_324_, 1, v_e_310_);
lean_closure_set(v___f_324_, 2, v_toBind_320_);
lean_closure_set(v___f_324_, 3, v___f_323_);
lean_closure_set(v___f_324_, 4, v___f_321_);
lean_closure_set(v___f_324_, 5, v_toApplicative_319_);
v___x_325_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_325_, 0, lean_box(0));
lean_closure_set(v___x_325_, 1, lean_box(0));
lean_closure_set(v___x_325_, 2, v_a_311_);
v___x_326_ = lean_apply_2(v_x_309_, lean_box(0), v___x_325_);
v___x_327_ = lean_apply_4(v_toBind_320_, lean_box(0), lean_box(0), v___x_326_, v___f_322_);
v___x_328_ = lean_apply_4(v_toBind_320_, lean_box(0), lean_box(0), v___x_327_, v___f_324_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4(lean_object* v_inst_329_, lean_object* v_inst_330_, lean_object* v_fn_331_, lean_object* v_x_332_, lean_object* v_x_333_, lean_object* v_arg_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_329_, v_inst_330_, v_fn_331_, v_x_332_, v_x_333_, v_arg_334_, v_a_335_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit(lean_object* v_m_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_fn_341_, lean_object* v_x_342_, lean_object* v_x_343_, lean_object* v_e_344_, lean_object* v_a_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_339_, v_inst_340_, v_fn_341_, v_x_342_, v_x_343_, v_e_344_, v_a_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___boxed(lean_object* v_m_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_fn_350_, lean_object* v_x_351_, lean_object* v_x_352_, lean_object* v_e_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit(v_m_347_, v_inst_348_, v_inst_349_, v_fn_350_, v_x_351_, v_x_352_, v_e_353_, v_a_354_);
lean_dec(v_a_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__0(lean_object* v_x_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_apply_1(v_x_356_, lean_box(0));
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__0___boxed(lean_object* v_x_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Meta_forEachExpr_x27___redArg___lam__0(v_x_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__1(lean_object* v_inst_371_, lean_object* v_00_u03b1_372_, lean_object* v_x_373_){
_start:
{
lean_object* v___f_374_; lean_object* v___x_375_; 
v___f_374_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_374_, 0, v_x_373_);
v___x_375_ = lean_apply_2(v_inst_371_, lean_box(0), v___f_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__2(lean_object* v_toPure_376_, lean_object* v_____x_377_){
_start:
{
lean_object* v_fst_378_; lean_object* v___x_379_; 
v_fst_378_ = lean_ctor_get(v_____x_377_, 0);
lean_inc(v_fst_378_);
lean_dec_ref(v_____x_377_);
v___x_379_ = lean_apply_2(v_toPure_376_, lean_box(0), v_fst_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__3(lean_object* v_a_380_, lean_object* v_toPure_381_, lean_object* v_s_382_){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v_a_380_);
lean_ctor_set(v___x_383_, 1, v_s_382_);
v___x_384_ = lean_apply_2(v_toPure_381_, lean_box(0), v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__4(lean_object* v_toPure_385_, lean_object* v_ref_386_, lean_object* v_x_387_, lean_object* v_toBind_388_, lean_object* v_a_389_){
_start:
{
lean_object* v___f_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___f_390_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__3), 3, 2);
lean_closure_set(v___f_390_, 0, v_a_389_);
lean_closure_set(v___f_390_, 1, v_toPure_385_);
v___x_391_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_391_, 0, lean_box(0));
lean_closure_set(v___x_391_, 1, lean_box(0));
lean_closure_set(v___x_391_, 2, v_ref_386_);
v___x_392_ = lean_apply_2(v_x_387_, lean_box(0), v___x_391_);
v___x_393_ = lean_apply_4(v_toBind_388_, lean_box(0), lean_box(0), v___x_392_, v___f_390_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__5(lean_object* v_toPure_394_, lean_object* v_x_395_, lean_object* v_toBind_396_, lean_object* v_inst_397_, lean_object* v_inst_398_, lean_object* v_fn_399_, lean_object* v_x_400_, lean_object* v_input_401_, lean_object* v_ref_402_){
_start:
{
lean_object* v___f_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
lean_inc(v_toBind_396_);
lean_inc(v_x_395_);
lean_inc(v_ref_402_);
v___f_403_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__4), 5, 4);
lean_closure_set(v___f_403_, 0, v_toPure_394_);
lean_closure_set(v___f_403_, 1, v_ref_402_);
lean_closure_set(v___f_403_, 2, v_x_395_);
lean_closure_set(v___f_403_, 3, v_toBind_396_);
v___x_404_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_397_, v_inst_398_, v_fn_399_, v_x_400_, v_x_395_, v_input_401_, v_ref_402_);
lean_dec(v_ref_402_);
v___x_405_ = lean_apply_4(v_toBind_396_, lean_box(0), lean_box(0), v___x_404_, v___f_403_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_box(0);
v___x_407_ = lean_unsigned_to_nat(16u);
v___x_408_ = lean_mk_array(v___x_407_, v___x_406_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__1(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___redArg___closed__0, &l_Lean_Meta_forEachExpr_x27___redArg___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__0);
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v___x_409_);
return v___x_411_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__2(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___redArg___closed__1, &l_Lean_Meta_forEachExpr_x27___redArg___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__1);
v___x_413_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_413_, 0, lean_box(0));
lean_closure_set(v___x_413_, 1, lean_box(0));
lean_closure_set(v___x_413_, 2, v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg(lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_inst_416_, lean_object* v_input_417_, lean_object* v_fn_418_){
_start:
{
lean_object* v_x_419_; lean_object* v_toApplicative_420_; lean_object* v_toBind_421_; lean_object* v_toPure_422_; lean_object* v_x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___f_426_; lean_object* v___f_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v_x_419_ = lean_box(0);
v_toApplicative_420_ = lean_ctor_get(v_inst_414_, 0);
v_toBind_421_ = lean_ctor_get(v_inst_414_, 1);
lean_inc_n(v_toBind_421_, 3);
v_toPure_422_ = lean_ctor_get(v_toApplicative_420_, 1);
lean_inc_n(v_toPure_422_, 2);
lean_inc(v_inst_415_);
v_x_423_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__1), 3, 1);
lean_closure_set(v_x_423_, 0, v_inst_415_);
v___x_424_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___redArg___closed__2, &l_Lean_Meta_forEachExpr_x27___redArg___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__2);
v___x_425_ = l_Lean_Meta_forEachExpr_x27___redArg___lam__1(v_inst_415_, lean_box(0), v___x_424_);
v___f_426_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_426_, 0, v_toPure_422_);
v___f_427_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__5), 9, 8);
lean_closure_set(v___f_427_, 0, v_toPure_422_);
lean_closure_set(v___f_427_, 1, v_x_423_);
lean_closure_set(v___f_427_, 2, v_toBind_421_);
lean_closure_set(v___f_427_, 3, v_inst_414_);
lean_closure_set(v___f_427_, 4, v_inst_416_);
lean_closure_set(v___f_427_, 5, v_fn_418_);
lean_closure_set(v___f_427_, 6, v_x_419_);
lean_closure_set(v___f_427_, 7, v_input_417_);
v___x_428_ = lean_apply_4(v_toBind_421_, lean_box(0), lean_box(0), v___x_425_, v___f_427_);
v___x_429_ = lean_apply_4(v_toBind_421_, lean_box(0), lean_box(0), v___x_428_, v___f_426_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27(lean_object* v_m_430_, lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_input_434_, lean_object* v_fn_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_Meta_forEachExpr_x27___redArg(v_inst_431_, v_inst_432_, v_inst_433_, v_input_434_, v_fn_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg___lam__0(lean_object* v_toPure_437_, lean_object* v_____r_438_){
_start:
{
uint8_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = 1;
v___x_440_ = lean_box(v___x_439_);
v___x_441_ = lean_apply_2(v_toPure_437_, lean_box(0), v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg___lam__1(lean_object* v_f_442_, lean_object* v_toBind_443_, lean_object* v___f_444_, lean_object* v_e_445_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = lean_apply_1(v_f_442_, v_e_445_);
v___x_447_ = lean_apply_4(v_toBind_443_, lean_box(0), lean_box(0), v___x_446_, v___f_444_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg(lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_e_451_, lean_object* v_f_452_){
_start:
{
lean_object* v_toApplicative_453_; lean_object* v_toBind_454_; lean_object* v_toPure_455_; lean_object* v___f_456_; lean_object* v___f_457_; lean_object* v___x_458_; 
v_toApplicative_453_ = lean_ctor_get(v_inst_448_, 0);
v_toBind_454_ = lean_ctor_get(v_inst_448_, 1);
v_toPure_455_ = lean_ctor_get(v_toApplicative_453_, 1);
lean_inc(v_toPure_455_);
v___f_456_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___redArg___lam__0), 2, 1);
lean_closure_set(v___f_456_, 0, v_toPure_455_);
lean_inc(v_toBind_454_);
v___f_457_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___redArg___lam__1), 4, 3);
lean_closure_set(v___f_457_, 0, v_f_452_);
lean_closure_set(v___f_457_, 1, v_toBind_454_);
lean_closure_set(v___f_457_, 2, v___f_456_);
v___x_458_ = l_Lean_Meta_forEachExpr_x27___redArg(v_inst_448_, v_inst_449_, v_inst_450_, v_e_451_, v___f_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr(lean_object* v_m_459_, lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_e_463_, lean_object* v_f_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_Meta_forEachExpr___redArg(v_inst_460_, v_inst_461_, v_inst_462_, v_e_463_, v_f_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0(lean_object* v_toPure_466_, lean_object* v_____do__lift_467_){
_start:
{
lean_object* v_userName_468_; uint8_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_userName_468_ = lean_ctor_get(v_____do__lift_467_, 0);
v___x_469_ = l_Lean_Name_isAnonymous(v_userName_468_);
v___x_470_ = lean_box(v___x_469_);
v___x_471_ = lean_apply_2(v_toPure_466_, lean_box(0), v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0___boxed(lean_object* v_toPure_472_, lean_object* v_____do__lift_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0(v_toPure_472_, v_____do__lift_473_);
lean_dec_ref(v_____do__lift_473_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg(lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_x_477_){
_start:
{
lean_object* v_toApplicative_478_; 
v_toApplicative_478_ = lean_ctor_get(v_inst_475_, 0);
lean_inc_ref(v_toApplicative_478_);
if (lean_obj_tag(v_x_477_) == 2)
{
lean_object* v_toBind_479_; lean_object* v_toPure_480_; lean_object* v_mvarId_481_; lean_object* v___f_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v_toBind_479_ = lean_ctor_get(v_inst_475_, 1);
lean_inc(v_toBind_479_);
lean_dec_ref(v_inst_475_);
v_toPure_480_ = lean_ctor_get(v_toApplicative_478_, 1);
lean_inc(v_toPure_480_);
lean_dec_ref(v_toApplicative_478_);
v_mvarId_481_ = lean_ctor_get(v_x_477_, 0);
lean_inc(v_mvarId_481_);
lean_dec_ref_known(v_x_477_, 1);
v___f_482_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_482_, 0, v_toPure_480_);
v___x_483_ = lean_alloc_closure((void*)(l_Lean_MVarId_getDecl___boxed), 6, 1);
lean_closure_set(v___x_483_, 0, v_mvarId_481_);
v___x_484_ = lean_apply_2(v_inst_476_, lean_box(0), v___x_483_);
v___x_485_ = lean_apply_4(v_toBind_479_, lean_box(0), lean_box(0), v___x_484_, v___f_482_);
return v___x_485_;
}
else
{
lean_object* v_toPure_486_; uint8_t v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
lean_dec_ref(v_x_477_);
lean_dec(v_inst_476_);
lean_dec_ref(v_inst_475_);
v_toPure_486_ = lean_ctor_get(v_toApplicative_478_, 1);
lean_inc(v_toPure_486_);
lean_dec_ref(v_toApplicative_478_);
v___x_487_ = 0;
v___x_488_ = lean_box(v___x_487_);
v___x_489_ = lean_apply_2(v_toPure_486_, lean_box(0), v___x_488_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName(lean_object* v_m_490_, lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_x_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg(v_inst_491_, v_inst_492_, v_x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0(lean_object* v_k_495_, lean_object* v_b_496_, lean_object* v_c_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; 
lean_inc(v___y_501_);
lean_inc_ref(v___y_500_);
lean_inc(v___y_499_);
lean_inc_ref(v___y_498_);
v___x_503_ = lean_apply_7(v_k_495_, v_b_496_, v_c_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, lean_box(0));
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0___boxed(lean_object* v_k_504_, lean_object* v_b_505_, lean_object* v_c_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0(v_k_504_, v_b_505_, v_c_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(lean_object* v_type_513_, lean_object* v_maxFVars_x3f_514_, lean_object* v_k_515_, uint8_t v_cleanupAnnotations_516_, uint8_t v_whnfType_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v___f_523_; lean_object* v___x_524_; 
v___f_523_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_523_, 0, v_k_515_);
v___x_524_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_513_, v_maxFVars_x3f_514_, v___f_523_, v_cleanupAnnotations_516_, v_whnfType_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_524_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_524_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
v_a_533_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_524_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_524_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___boxed(lean_object* v_type_541_, lean_object* v_maxFVars_x3f_542_, lean_object* v_k_543_, lean_object* v_cleanupAnnotations_544_, lean_object* v_whnfType_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_551_; uint8_t v_whnfType_boxed_552_; lean_object* v_res_553_; 
v_cleanupAnnotations_boxed_551_ = lean_unbox(v_cleanupAnnotations_544_);
v_whnfType_boxed_552_ = lean_unbox(v_whnfType_545_);
v_res_553_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(v_type_541_, v_maxFVars_x3f_542_, v_k_543_, v_cleanupAnnotations_boxed_551_, v_whnfType_boxed_552_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0(lean_object* v_00_u03b1_554_, lean_object* v_type_555_, lean_object* v_maxFVars_x3f_556_, lean_object* v_k_557_, uint8_t v_cleanupAnnotations_558_, uint8_t v_whnfType_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(v_type_555_, v_maxFVars_x3f_556_, v_k_557_, v_cleanupAnnotations_558_, v_whnfType_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___boxed(lean_object* v_00_u03b1_566_, lean_object* v_type_567_, lean_object* v_maxFVars_x3f_568_, lean_object* v_k_569_, lean_object* v_cleanupAnnotations_570_, lean_object* v_whnfType_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_577_; uint8_t v_whnfType_boxed_578_; lean_object* v_res_579_; 
v_cleanupAnnotations_boxed_577_ = lean_unbox(v_cleanupAnnotations_570_);
v_whnfType_boxed_578_ = lean_unbox(v_whnfType_571_);
v_res_579_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0(v_00_u03b1_566_, v_type_567_, v_maxFVars_x3f_568_, v_k_569_, v_cleanupAnnotations_boxed_577_, v_whnfType_boxed_578_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(lean_object* v_e_580_, lean_object* v___y_581_){
_start:
{
uint8_t v___x_583_; 
v___x_583_ = l_Lean_Expr_hasMVar(v_e_580_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v_e_580_);
return v___x_584_;
}
else
{
lean_object* v___x_585_; lean_object* v_mctx_586_; lean_object* v___x_587_; lean_object* v_fst_588_; lean_object* v_snd_589_; lean_object* v___x_590_; lean_object* v_cache_591_; lean_object* v_zetaDeltaFVarIds_592_; lean_object* v_postponed_593_; lean_object* v_diag_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_603_; 
v___x_585_ = lean_st_ref_get(v___y_581_);
v_mctx_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc_ref(v_mctx_586_);
lean_dec(v___x_585_);
v___x_587_ = l_Lean_instantiateMVarsCore(v_mctx_586_, v_e_580_);
v_fst_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_fst_588_);
v_snd_589_ = lean_ctor_get(v___x_587_, 1);
lean_inc(v_snd_589_);
lean_dec_ref(v___x_587_);
v___x_590_ = lean_st_ref_take(v___y_581_);
v_cache_591_ = lean_ctor_get(v___x_590_, 1);
v_zetaDeltaFVarIds_592_ = lean_ctor_get(v___x_590_, 2);
v_postponed_593_ = lean_ctor_get(v___x_590_, 3);
v_diag_594_ = lean_ctor_get(v___x_590_, 4);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; 
v_unused_604_ = lean_ctor_get(v___x_590_, 0);
lean_dec(v_unused_604_);
v___x_596_ = v___x_590_;
v_isShared_597_ = v_isSharedCheck_603_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_diag_594_);
lean_inc(v_postponed_593_);
lean_inc(v_zetaDeltaFVarIds_592_);
lean_inc(v_cache_591_);
lean_dec(v___x_590_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_603_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v_snd_589_);
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_snd_589_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_cache_591_);
lean_ctor_set(v_reuseFailAlloc_602_, 2, v_zetaDeltaFVarIds_592_);
lean_ctor_set(v_reuseFailAlloc_602_, 3, v_postponed_593_);
lean_ctor_set(v_reuseFailAlloc_602_, 4, v_diag_594_);
v___x_599_ = v_reuseFailAlloc_602_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_st_ref_put(v___y_581_, v___x_599_);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v_fst_588_);
return v___x_601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg___boxed(lean_object* v_e_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(v_e_605_, v___y_606_);
lean_dec(v___y_606_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3(lean_object* v_e_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(v_e_609_, v___y_611_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___boxed(lean_object* v_e_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3(v_e_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0(lean_object* v_a_623_, lean_object* v___x_624_, lean_object* v___x_625_, lean_object* v_val_626_, lean_object* v___x_627_, lean_object* v_xs_628_, lean_object* v_x_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = lean_array_get_size(v_xs_628_);
v___x_636_ = lean_nat_dec_lt(v_a_623_, v___x_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
lean_dec(v___x_627_);
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_624_);
return v___x_637_;
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_array_get_borrowed(v___x_625_, v_xs_628_, v_a_623_);
v___x_639_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_638_, v___y_630_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_639_, 1);
v___x_641_ = l_Lean_LocalDecl_userName(v_a_640_);
lean_dec(v_a_640_);
v___x_642_ = l_Lean_Core_mkFreshUserName(v___x_641_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_668_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_668_ == 0)
{
v___x_645_ = v___x_642_;
v_isShared_646_ = v_isSharedCheck_668_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_642_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_668_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v_mctx_651_; lean_object* v_cache_652_; lean_object* v_zetaDeltaFVarIds_653_; lean_object* v_postponed_654_; lean_object* v_diag_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_667_; 
v___x_647_ = lean_st_ref_take(v_val_626_);
lean_inc(v___x_627_);
v___x_648_ = lean_array_push(v___x_647_, v___x_627_);
v___x_649_ = lean_st_ref_put(v_val_626_, v___x_648_);
v___x_650_ = lean_st_ref_take(v___y_631_);
v_mctx_651_ = lean_ctor_get(v___x_650_, 0);
v_cache_652_ = lean_ctor_get(v___x_650_, 1);
v_zetaDeltaFVarIds_653_ = lean_ctor_get(v___x_650_, 2);
v_postponed_654_ = lean_ctor_get(v___x_650_, 3);
v_diag_655_ = lean_ctor_get(v___x_650_, 4);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_667_ == 0)
{
v___x_657_ = v___x_650_;
v_isShared_658_ = v_isSharedCheck_667_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_diag_655_);
lean_inc(v_postponed_654_);
lean_inc(v_zetaDeltaFVarIds_653_);
lean_inc(v_cache_652_);
lean_inc(v_mctx_651_);
lean_dec(v___x_650_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_667_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = l_Lean_MetavarContext_setMVarUserNameTemporarily(v_mctx_651_, v___x_627_, v_a_643_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_659_);
v___x_661_ = v___x_657_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_cache_652_);
lean_ctor_set(v_reuseFailAlloc_666_, 2, v_zetaDeltaFVarIds_653_);
lean_ctor_set(v_reuseFailAlloc_666_, 3, v_postponed_654_);
lean_ctor_set(v_reuseFailAlloc_666_, 4, v_diag_655_);
v___x_661_ = v_reuseFailAlloc_666_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = lean_st_ref_put(v___y_631_, v___x_661_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_624_);
v___x_664_ = v___x_645_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_624_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec(v___x_627_);
v_a_669_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_642_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_642_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
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
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec(v___x_627_);
v_a_677_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_639_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_639_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0___boxed(lean_object* v_a_685_, lean_object* v___x_686_, lean_object* v___x_687_, lean_object* v_val_688_, lean_object* v___x_689_, lean_object* v_xs_690_, lean_object* v_x_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0(v_a_685_, v___x_686_, v___x_687_, v_val_688_, v___x_689_, v_xs_690_, v_x_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec_ref(v_x_691_);
lean_dec_ref(v_xs_690_);
lean_dec(v_val_688_);
lean_dec_ref(v___x_687_);
lean_dec(v_a_685_);
return v_res_697_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(lean_object* v_a_698_, lean_object* v_as_699_, size_t v_i_700_, size_t v_stop_701_){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = lean_usize_dec_eq(v_i_700_, v_stop_701_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_703_ = lean_array_uget_borrowed(v_as_699_, v_i_700_);
v___x_704_ = lean_expr_eqv(v_a_698_, v___x_703_);
if (v___x_704_ == 0)
{
size_t v___x_705_; size_t v___x_706_; 
v___x_705_ = ((size_t)1ULL);
v___x_706_ = lean_usize_add(v_i_700_, v___x_705_);
v_i_700_ = v___x_706_;
goto _start;
}
else
{
return v___x_704_;
}
}
else
{
uint8_t v___x_708_; 
v___x_708_ = 0;
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1___boxed(lean_object* v_a_709_, lean_object* v_as_710_, lean_object* v_i_711_, lean_object* v_stop_712_){
_start:
{
size_t v_i_boxed_713_; size_t v_stop_boxed_714_; uint8_t v_res_715_; lean_object* v_r_716_; 
v_i_boxed_713_ = lean_unbox_usize(v_i_711_);
lean_dec(v_i_711_);
v_stop_boxed_714_ = lean_unbox_usize(v_stop_712_);
lean_dec(v_stop_712_);
v_res_715_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(v_a_709_, v_as_710_, v_i_boxed_713_, v_stop_boxed_714_);
lean_dec_ref(v_as_710_);
lean_dec_ref(v_a_709_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(lean_object* v_as_717_, lean_object* v_a_718_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = lean_array_get_size(v_as_717_);
v___x_721_ = lean_nat_dec_lt(v___x_719_, v___x_720_);
if (v___x_721_ == 0)
{
return v___x_721_;
}
else
{
if (v___x_721_ == 0)
{
return v___x_721_;
}
else
{
size_t v___x_722_; size_t v___x_723_; uint8_t v___x_724_; 
v___x_722_ = ((size_t)0ULL);
v___x_723_ = lean_usize_of_nat(v___x_720_);
v___x_724_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(v_a_718_, v_as_717_, v___x_722_, v___x_723_);
return v___x_724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1___boxed(lean_object* v_as_725_, lean_object* v_a_726_){
_start:
{
uint8_t v_res_727_; lean_object* v_r_728_; 
v_res_727_ = l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(v_as_725_, v_a_726_);
lean_dec_ref(v_a_726_);
lean_dec_ref(v_as_725_);
v_r_728_ = lean_box(v_res_727_);
return v_r_728_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(lean_object* v_upperBound_729_, lean_object* v___x_730_, lean_object* v_val_731_, lean_object* v_e_732_, lean_object* v_isTarget_733_, lean_object* v_a_734_, lean_object* v_b_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_a_742_; uint8_t v___x_746_; 
v___x_746_ = lean_nat_dec_lt(v_a_734_, v_upperBound_729_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; 
lean_dec(v_a_734_);
lean_dec(v_val_731_);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v_b_735_);
return v___x_747_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___y_752_; uint8_t v___x_783_; 
v___x_748_ = lean_box(0);
v___x_749_ = l_Lean_instInhabitedExpr;
v___x_750_ = lean_array_fget_borrowed(v___x_730_, v_a_734_);
v___x_783_ = l_Lean_Expr_isMVar(v___x_750_);
if (v___x_783_ == 0)
{
v___y_752_ = v___x_783_;
goto v___jp_751_;
}
else
{
uint8_t v___x_784_; 
v___x_784_ = l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(v_isTarget_733_, v___x_750_);
v___y_752_ = v___x_784_;
goto v___jp_751_;
}
v___jp_751_:
{
if (v___y_752_ == 0)
{
v_a_742_ = v___x_748_;
goto v___jp_741_;
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = l_Lean_Expr_mvarId_x21(v___x_750_);
lean_inc(v___x_753_);
v___x_754_ = l_Lean_MVarId_getDecl(v___x_753_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v_userName_756_; uint8_t v___x_757_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
lean_dec_ref_known(v___x_754_, 1);
v_userName_756_ = lean_ctor_get(v_a_755_, 0);
lean_inc(v_userName_756_);
lean_dec(v_a_755_);
v___x_757_ = l_Lean_Name_isAnonymous(v_userName_756_);
lean_dec(v_userName_756_);
if (v___x_757_ == 0)
{
lean_dec(v___x_753_);
v_a_742_ = v___x_748_;
goto v___jp_741_;
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = l_Lean_Expr_getAppFn(v_e_732_);
lean_inc(v___y_739_);
lean_inc_ref(v___y_738_);
lean_inc(v___y_737_);
lean_inc_ref(v___y_736_);
v___x_759_ = lean_infer_type(v___x_758_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___f_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; lean_object* v___x_766_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref_known(v___x_759_, 1);
lean_inc(v_val_731_);
lean_inc(v_a_734_);
v___f_761_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_761_, 0, v_a_734_);
lean_closure_set(v___f_761_, 1, v___x_748_);
lean_closure_set(v___f_761_, 2, v___x_749_);
lean_closure_set(v___f_761_, 3, v_val_731_);
lean_closure_set(v___f_761_, 4, v___x_753_);
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_nat_add(v_a_734_, v___x_762_);
v___x_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
v___x_765_ = 0;
v___x_766_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(v_a_760_, v___x_764_, v___f_761_, v___x_765_, v___x_765_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_dec_ref_known(v___x_766_, 1);
v_a_742_ = v___x_748_;
goto v___jp_741_;
}
else
{
lean_dec(v_a_734_);
lean_dec(v_val_731_);
return v___x_766_;
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec(v___x_753_);
lean_dec(v_a_734_);
lean_dec(v_val_731_);
v_a_767_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_759_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_759_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec(v___x_753_);
lean_dec(v_a_734_);
lean_dec(v_val_731_);
v_a_775_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_754_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_754_);
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
}
v___jp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_unsigned_to_nat(1u);
v___x_744_ = lean_nat_add(v_a_734_, v___x_743_);
lean_dec(v_a_734_);
v_a_734_ = v___x_744_;
v_b_735_ = v_a_742_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___boxed(lean_object* v_upperBound_785_, lean_object* v___x_786_, lean_object* v_val_787_, lean_object* v_e_788_, lean_object* v_isTarget_789_, lean_object* v_a_790_, lean_object* v_b_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(v_upperBound_785_, v___x_786_, v_val_787_, v_e_788_, v_isTarget_789_, v_a_790_, v_b_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec_ref(v_isTarget_789_);
lean_dec_ref(v_e_788_);
lean_dec_ref(v___x_786_);
lean_dec(v_upperBound_785_);
return v_res_797_;
}
}
static lean_object* _init_l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0(void){
_start:
{
lean_object* v___x_798_; lean_object* v_dummy_799_; 
v___x_798_ = lean_box(0);
v_dummy_799_ = l_Lean_Expr_sort___override(v___x_798_);
return v_dummy_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___lam__0(lean_object* v_val_800_, lean_object* v_isTarget_801_, lean_object* v___x_802_, lean_object* v_e_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
uint8_t v___x_809_; 
v___x_809_ = l_Lean_Expr_isApp(v_e_803_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec_ref(v_e_803_);
lean_dec(v___x_802_);
lean_dec(v_val_800_);
v___x_810_ = lean_box(0);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
return v___x_811_;
}
else
{
lean_object* v_dummy_812_; lean_object* v_nargs_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v_dummy_812_ = lean_obj_once(&l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0, &l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0_once, _init_l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0);
v_nargs_813_ = l_Lean_Expr_getAppNumArgs(v_e_803_);
lean_inc(v_nargs_813_);
v___x_814_ = lean_mk_array(v_nargs_813_, v_dummy_812_);
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = lean_nat_sub(v_nargs_813_, v___x_815_);
lean_dec(v_nargs_813_);
lean_inc_ref(v_e_803_);
v___x_817_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_803_, v___x_814_, v___x_816_);
v___x_818_ = lean_array_get_size(v___x_817_);
v___x_819_ = lean_box(0);
v___x_820_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(v___x_818_, v___x_817_, v_val_800_, v_e_803_, v_isTarget_801_, v___x_802_, v___x_819_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec_ref(v_e_803_);
lean_dec_ref(v___x_817_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v___x_820_, 0);
lean_dec(v_unused_828_);
v___x_822_ = v___x_820_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_dec(v___x_820_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_819_);
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_819_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
else
{
return v___x_820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___lam__0___boxed(lean_object* v_val_829_, lean_object* v_isTarget_830_, lean_object* v___x_831_, lean_object* v_e_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_Meta_setMVarUserNamesAt___lam__0(v_val_829_, v_isTarget_830_, v___x_831_, v_e_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec_ref(v_isTarget_830_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0(lean_object* v_k_839_, lean_object* v___y_840_, lean_object* v_b_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; 
lean_inc(v___y_845_);
lean_inc_ref(v___y_844_);
lean_inc(v___y_843_);
lean_inc_ref(v___y_842_);
lean_inc(v___y_840_);
v___x_847_ = lean_apply_7(v_k_839_, v_b_841_, v___y_840_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, lean_box(0));
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0___boxed(lean_object* v_k_848_, lean_object* v___y_849_, lean_object* v_b_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0(v_k_848_, v___y_849_, v_b_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_849_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(lean_object* v_name_857_, uint8_t v_bi_858_, lean_object* v_type_859_, lean_object* v_k_860_, uint8_t v_kind_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v___f_868_; lean_object* v___x_869_; 
lean_inc(v___y_862_);
v___f_868_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_868_, 0, v_k_860_);
lean_closure_set(v___f_868_, 1, v___y_862_);
v___x_869_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_857_, v_bi_858_, v_type_859_, v___f_868_, v_kind_861_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
if (lean_obj_tag(v___x_869_) == 0)
{
return v___x_869_;
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___boxed(lean_object* v_name_878_, lean_object* v_bi_879_, lean_object* v_type_880_, lean_object* v_k_881_, lean_object* v_kind_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
uint8_t v_bi_boxed_889_; uint8_t v_kind_boxed_890_; lean_object* v_res_891_; 
v_bi_boxed_889_ = lean_unbox(v_bi_879_);
v_kind_boxed_890_ = lean_unbox(v_kind_882_);
v_res_891_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_name_878_, v_bi_boxed_889_, v_type_880_, v_k_881_, v_kind_boxed_890_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0___boxed(lean_object* v_fvars_892_, lean_object* v_f_893_, lean_object* v_body_894_, lean_object* v_x_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0(v_fvars_892_, v_f_893_, v_body_894_, v_x_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(lean_object* v_f_903_, lean_object* v_fvars_904_, lean_object* v_a_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
if (lean_obj_tag(v_a_905_) == 6)
{
lean_object* v_binderName_912_; lean_object* v_binderType_913_; lean_object* v_body_914_; uint8_t v_binderInfo_915_; lean_object* v_d_916_; lean_object* v___x_917_; 
v_binderName_912_ = lean_ctor_get(v_a_905_, 0);
lean_inc(v_binderName_912_);
v_binderType_913_ = lean_ctor_get(v_a_905_, 1);
lean_inc_ref(v_binderType_913_);
v_body_914_ = lean_ctor_get(v_a_905_, 2);
lean_inc_ref(v_body_914_);
v_binderInfo_915_ = lean_ctor_get_uint8(v_a_905_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_905_, 3);
v_d_916_ = lean_expr_instantiate_rev(v_binderType_913_, v_fvars_904_);
lean_dec_ref(v_binderType_913_);
lean_inc_ref(v_f_903_);
lean_inc(v___y_910_);
lean_inc_ref(v___y_909_);
lean_inc(v___y_908_);
lean_inc_ref(v___y_907_);
lean_inc(v___y_906_);
lean_inc_ref(v_d_916_);
v___x_917_ = lean_apply_7(v_f_903_, v_d_916_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, lean_box(0));
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v___f_918_; uint8_t v___x_919_; lean_object* v___x_920_; 
lean_dec_ref_known(v___x_917_, 1);
v___f_918_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0___boxed), 10, 3);
lean_closure_set(v___f_918_, 0, v_fvars_904_);
lean_closure_set(v___f_918_, 1, v_f_903_);
lean_closure_set(v___f_918_, 2, v_body_914_);
v___x_919_ = 0;
v___x_920_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_binderName_912_, v_binderInfo_915_, v_d_916_, v___f_918_, v___x_919_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
return v___x_920_;
}
else
{
lean_dec_ref(v_d_916_);
lean_dec_ref(v_body_914_);
lean_dec(v_binderName_912_);
lean_dec_ref(v_fvars_904_);
lean_dec_ref(v_f_903_);
return v___x_917_;
}
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_expr_instantiate_rev(v_a_905_, v_fvars_904_);
lean_dec_ref(v_fvars_904_);
lean_dec_ref(v_a_905_);
lean_inc(v___y_910_);
lean_inc_ref(v___y_909_);
lean_inc(v___y_908_);
lean_inc_ref(v___y_907_);
lean_inc(v___y_906_);
v___x_922_ = lean_apply_7(v_f_903_, v___x_921_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, lean_box(0));
return v___x_922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0(lean_object* v_fvars_923_, lean_object* v_f_924_, lean_object* v_body_925_, lean_object* v_x_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = lean_array_push(v_fvars_923_, v_x_926_);
v___x_934_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(v_f_924_, v___x_933_, v_body_925_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___boxed(lean_object* v_f_935_, lean_object* v_fvars_936_, lean_object* v_a_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(v_f_935_, v_fvars_936_, v_a_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(lean_object* v_f_945_, lean_object* v_e_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_954_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(v_f_945_, v___x_953_, v_e_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10___boxed(lean_object* v_f_955_, lean_object* v_e_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(v_f_955_, v_e_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_object* v_00_u03b1_964_, lean_object* v_x_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_apply_1(v_x_965_, lean_box(0));
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0___boxed(lean_object* v_00_u03b1_973_, lean_object* v_x_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(v_00_u03b1_973_, v_x_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0___boxed(lean_object* v_fvars_981_, lean_object* v_f_982_, lean_object* v_body_983_, lean_object* v_x_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0(v_fvars_981_, v_f_982_, v_body_983_, v_x_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(lean_object* v_f_992_, lean_object* v_fvars_993_, lean_object* v_a_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
if (lean_obj_tag(v_a_994_) == 7)
{
lean_object* v_binderName_1001_; lean_object* v_binderType_1002_; lean_object* v_body_1003_; uint8_t v_binderInfo_1004_; lean_object* v_d_1005_; lean_object* v___x_1006_; 
v_binderName_1001_ = lean_ctor_get(v_a_994_, 0);
lean_inc(v_binderName_1001_);
v_binderType_1002_ = lean_ctor_get(v_a_994_, 1);
lean_inc_ref(v_binderType_1002_);
v_body_1003_ = lean_ctor_get(v_a_994_, 2);
lean_inc_ref(v_body_1003_);
v_binderInfo_1004_ = lean_ctor_get_uint8(v_a_994_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_994_, 3);
v_d_1005_ = lean_expr_instantiate_rev(v_binderType_1002_, v_fvars_993_);
lean_dec_ref(v_binderType_1002_);
lean_inc_ref(v_f_992_);
lean_inc(v___y_999_);
lean_inc_ref(v___y_998_);
lean_inc(v___y_997_);
lean_inc_ref(v___y_996_);
lean_inc(v___y_995_);
lean_inc_ref(v_d_1005_);
v___x_1006_ = lean_apply_7(v_f_992_, v_d_1005_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, lean_box(0));
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v___f_1007_; uint8_t v___x_1008_; lean_object* v___x_1009_; 
lean_dec_ref_known(v___x_1006_, 1);
v___f_1007_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1007_, 0, v_fvars_993_);
lean_closure_set(v___f_1007_, 1, v_f_992_);
lean_closure_set(v___f_1007_, 2, v_body_1003_);
v___x_1008_ = 0;
v___x_1009_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_binderName_1001_, v_binderInfo_1004_, v_d_1005_, v___f_1007_, v___x_1008_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1009_;
}
else
{
lean_dec_ref(v_d_1005_);
lean_dec_ref(v_body_1003_);
lean_dec(v_binderName_1001_);
lean_dec_ref(v_fvars_993_);
lean_dec_ref(v_f_992_);
return v___x_1006_;
}
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_expr_instantiate_rev(v_a_994_, v_fvars_993_);
lean_dec_ref(v_fvars_993_);
lean_dec_ref(v_a_994_);
lean_inc(v___y_999_);
lean_inc_ref(v___y_998_);
lean_inc(v___y_997_);
lean_inc_ref(v___y_996_);
lean_inc(v___y_995_);
v___x_1011_ = lean_apply_7(v_f_992_, v___x_1010_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, lean_box(0));
return v___x_1011_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0(lean_object* v_fvars_1012_, lean_object* v_f_1013_, lean_object* v_body_1014_, lean_object* v_x_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_array_push(v_fvars_1012_, v_x_1015_);
v___x_1023_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(v_f_1013_, v___x_1022_, v_body_1014_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___boxed(lean_object* v_f_1024_, lean_object* v_fvars_1025_, lean_object* v_a_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(v_f_1024_, v_fvars_1025_, v_a_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(lean_object* v_f_1034_, lean_object* v_e_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_1043_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(v_f_1034_, v___x_1042_, v_e_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9___boxed(lean_object* v_f_1044_, lean_object* v_e_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(v_f_1044_, v_e_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_a_1053_, lean_object* v_x_1054_){
_start:
{
if (lean_obj_tag(v_x_1054_) == 0)
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_box(0);
return v___x_1055_;
}
else
{
lean_object* v_key_1056_; lean_object* v_value_1057_; lean_object* v_tail_1058_; uint8_t v___x_1059_; 
v_key_1056_ = lean_ctor_get(v_x_1054_, 0);
v_value_1057_ = lean_ctor_get(v_x_1054_, 1);
v_tail_1058_ = lean_ctor_get(v_x_1054_, 2);
v___x_1059_ = lean_expr_eqv(v_key_1056_, v_a_1053_);
if (v___x_1059_ == 0)
{
v_x_1054_ = v_tail_1058_;
goto _start;
}
else
{
lean_object* v___x_1061_; 
lean_inc(v_value_1057_);
v___x_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1061_, 0, v_value_1057_);
return v___x_1061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_a_1062_, lean_object* v_x_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(v_a_1062_, v_x_1063_);
lean_dec(v_x_1063_);
lean_dec_ref(v_a_1062_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_m_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v_buckets_1067_; lean_object* v___x_1068_; uint64_t v___x_1069_; uint64_t v___x_1070_; uint64_t v___x_1071_; uint64_t v_fold_1072_; uint64_t v___x_1073_; uint64_t v___x_1074_; uint64_t v___x_1075_; size_t v___x_1076_; size_t v___x_1077_; size_t v___x_1078_; size_t v___x_1079_; size_t v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v_buckets_1067_ = lean_ctor_get(v_m_1065_, 1);
v___x_1068_ = lean_array_get_size(v_buckets_1067_);
v___x_1069_ = l_Lean_Expr_hash(v_a_1066_);
v___x_1070_ = 32ULL;
v___x_1071_ = lean_uint64_shift_right(v___x_1069_, v___x_1070_);
v_fold_1072_ = lean_uint64_xor(v___x_1069_, v___x_1071_);
v___x_1073_ = 16ULL;
v___x_1074_ = lean_uint64_shift_right(v_fold_1072_, v___x_1073_);
v___x_1075_ = lean_uint64_xor(v_fold_1072_, v___x_1074_);
v___x_1076_ = lean_uint64_to_usize(v___x_1075_);
v___x_1077_ = lean_usize_of_nat(v___x_1068_);
v___x_1078_ = ((size_t)1ULL);
v___x_1079_ = lean_usize_sub(v___x_1077_, v___x_1078_);
v___x_1080_ = lean_usize_land(v___x_1076_, v___x_1079_);
v___x_1081_ = lean_array_uget_borrowed(v_buckets_1067_, v___x_1080_);
v___x_1082_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(v_a_1066_, v___x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_m_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_m_1083_, v_a_1084_);
lean_dec_ref(v_a_1084_);
lean_dec_ref(v_m_1083_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(lean_object* v_a_1086_, lean_object* v_b_1087_, lean_object* v_x_1088_){
_start:
{
if (lean_obj_tag(v_x_1088_) == 0)
{
lean_dec(v_b_1087_);
lean_dec_ref(v_a_1086_);
return v_x_1088_;
}
else
{
lean_object* v_key_1089_; lean_object* v_value_1090_; lean_object* v_tail_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1103_; 
v_key_1089_ = lean_ctor_get(v_x_1088_, 0);
v_value_1090_ = lean_ctor_get(v_x_1088_, 1);
v_tail_1091_ = lean_ctor_get(v_x_1088_, 2);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_x_1088_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1093_ = v_x_1088_;
v_isShared_1094_ = v_isSharedCheck_1103_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_tail_1091_);
lean_inc(v_value_1090_);
lean_inc(v_key_1089_);
lean_dec(v_x_1088_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1103_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
uint8_t v___x_1095_; 
v___x_1095_ = lean_expr_eqv(v_key_1089_, v_a_1086_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1096_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(v_a_1086_, v_b_1087_, v_tail_1091_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 2, v___x_1096_);
v___x_1098_ = v___x_1093_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_key_1089_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_value_1090_);
lean_ctor_set(v_reuseFailAlloc_1099_, 2, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
else
{
lean_object* v___x_1101_; 
lean_dec(v_value_1090_);
lean_dec(v_key_1089_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v_b_1087_);
lean_ctor_set(v___x_1093_, 0, v_a_1086_);
v___x_1101_ = v___x_1093_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1086_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_b_1087_);
lean_ctor_set(v_reuseFailAlloc_1102_, 2, v_tail_1091_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16___redArg(lean_object* v_x_1104_, lean_object* v_x_1105_){
_start:
{
if (lean_obj_tag(v_x_1105_) == 0)
{
return v_x_1104_;
}
else
{
lean_object* v_key_1106_; lean_object* v_value_1107_; lean_object* v_tail_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1131_; 
v_key_1106_ = lean_ctor_get(v_x_1105_, 0);
v_value_1107_ = lean_ctor_get(v_x_1105_, 1);
v_tail_1108_ = lean_ctor_get(v_x_1105_, 2);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_x_1105_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1110_ = v_x_1105_;
v_isShared_1111_ = v_isSharedCheck_1131_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_tail_1108_);
lean_inc(v_value_1107_);
lean_inc(v_key_1106_);
lean_dec(v_x_1105_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1131_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; uint64_t v___x_1113_; uint64_t v___x_1114_; uint64_t v___x_1115_; uint64_t v_fold_1116_; uint64_t v___x_1117_; uint64_t v___x_1118_; uint64_t v___x_1119_; size_t v___x_1120_; size_t v___x_1121_; size_t v___x_1122_; size_t v___x_1123_; size_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1112_ = lean_array_get_size(v_x_1104_);
v___x_1113_ = l_Lean_Expr_hash(v_key_1106_);
v___x_1114_ = 32ULL;
v___x_1115_ = lean_uint64_shift_right(v___x_1113_, v___x_1114_);
v_fold_1116_ = lean_uint64_xor(v___x_1113_, v___x_1115_);
v___x_1117_ = 16ULL;
v___x_1118_ = lean_uint64_shift_right(v_fold_1116_, v___x_1117_);
v___x_1119_ = lean_uint64_xor(v_fold_1116_, v___x_1118_);
v___x_1120_ = lean_uint64_to_usize(v___x_1119_);
v___x_1121_ = lean_usize_of_nat(v___x_1112_);
v___x_1122_ = ((size_t)1ULL);
v___x_1123_ = lean_usize_sub(v___x_1121_, v___x_1122_);
v___x_1124_ = lean_usize_land(v___x_1120_, v___x_1123_);
v___x_1125_ = lean_array_uget_borrowed(v_x_1104_, v___x_1124_);
lean_inc(v___x_1125_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 2, v___x_1125_);
v___x_1127_ = v___x_1110_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_key_1106_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_value_1107_);
lean_ctor_set(v_reuseFailAlloc_1130_, 2, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_array_uset(v_x_1104_, v___x_1124_, v___x_1127_);
v_x_1104_ = v___x_1128_;
v_x_1105_ = v_tail_1108_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12___redArg(lean_object* v_i_1132_, lean_object* v_source_1133_, lean_object* v_target_1134_){
_start:
{
lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = lean_array_get_size(v_source_1133_);
v___x_1136_ = lean_nat_dec_lt(v_i_1132_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_dec_ref(v_source_1133_);
lean_dec(v_i_1132_);
return v_target_1134_;
}
else
{
lean_object* v_es_1137_; lean_object* v___x_1138_; lean_object* v_source_1139_; lean_object* v_target_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_es_1137_ = lean_array_fget(v_source_1133_, v_i_1132_);
v___x_1138_ = lean_box(0);
v_source_1139_ = lean_array_fset(v_source_1133_, v_i_1132_, v___x_1138_);
v_target_1140_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16___redArg(v_target_1134_, v_es_1137_);
v___x_1141_ = lean_unsigned_to_nat(1u);
v___x_1142_ = lean_nat_add(v_i_1132_, v___x_1141_);
lean_dec(v_i_1132_);
v_i_1132_ = v___x_1142_;
v_source_1133_ = v_source_1139_;
v_target_1134_ = v_target_1140_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11___redArg(lean_object* v_data_1144_){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v_nbuckets_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1145_ = lean_array_get_size(v_data_1144_);
v___x_1146_ = lean_unsigned_to_nat(2u);
v_nbuckets_1147_ = lean_nat_mul(v___x_1145_, v___x_1146_);
v___x_1148_ = lean_unsigned_to_nat(0u);
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_mk_array(v_nbuckets_1147_, v___x_1149_);
v___x_1151_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12___redArg(v___x_1148_, v_data_1144_, v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(lean_object* v_a_1152_, lean_object* v_x_1153_){
_start:
{
if (lean_obj_tag(v_x_1153_) == 0)
{
uint8_t v___x_1154_; 
v___x_1154_ = 0;
return v___x_1154_;
}
else
{
lean_object* v_key_1155_; lean_object* v_tail_1156_; uint8_t v___x_1157_; 
v_key_1155_ = lean_ctor_get(v_x_1153_, 0);
v_tail_1156_ = lean_ctor_get(v_x_1153_, 2);
v___x_1157_ = lean_expr_eqv(v_key_1155_, v_a_1152_);
if (v___x_1157_ == 0)
{
v_x_1153_ = v_tail_1156_;
goto _start;
}
else
{
return v___x_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_a_1159_, lean_object* v_x_1160_){
_start:
{
uint8_t v_res_1161_; lean_object* v_r_1162_; 
v_res_1161_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_a_1159_, v_x_1160_);
lean_dec(v_x_1160_);
lean_dec_ref(v_a_1159_);
v_r_1162_ = lean_box(v_res_1161_);
return v_r_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(lean_object* v_m_1163_, lean_object* v_a_1164_, lean_object* v_b_1165_){
_start:
{
lean_object* v_size_1166_; lean_object* v_buckets_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1210_; 
v_size_1166_ = lean_ctor_get(v_m_1163_, 0);
v_buckets_1167_ = lean_ctor_get(v_m_1163_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_m_1163_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1169_ = v_m_1163_;
v_isShared_1170_ = v_isSharedCheck_1210_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_buckets_1167_);
lean_inc(v_size_1166_);
lean_dec(v_m_1163_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1210_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; uint64_t v___x_1172_; uint64_t v___x_1173_; uint64_t v___x_1174_; uint64_t v_fold_1175_; uint64_t v___x_1176_; uint64_t v___x_1177_; uint64_t v___x_1178_; size_t v___x_1179_; size_t v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; size_t v___x_1183_; lean_object* v_bkt_1184_; uint8_t v___x_1185_; 
v___x_1171_ = lean_array_get_size(v_buckets_1167_);
v___x_1172_ = l_Lean_Expr_hash(v_a_1164_);
v___x_1173_ = 32ULL;
v___x_1174_ = lean_uint64_shift_right(v___x_1172_, v___x_1173_);
v_fold_1175_ = lean_uint64_xor(v___x_1172_, v___x_1174_);
v___x_1176_ = 16ULL;
v___x_1177_ = lean_uint64_shift_right(v_fold_1175_, v___x_1176_);
v___x_1178_ = lean_uint64_xor(v_fold_1175_, v___x_1177_);
v___x_1179_ = lean_uint64_to_usize(v___x_1178_);
v___x_1180_ = lean_usize_of_nat(v___x_1171_);
v___x_1181_ = ((size_t)1ULL);
v___x_1182_ = lean_usize_sub(v___x_1180_, v___x_1181_);
v___x_1183_ = lean_usize_land(v___x_1179_, v___x_1182_);
v_bkt_1184_ = lean_array_uget_borrowed(v_buckets_1167_, v___x_1183_);
v___x_1185_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_a_1164_, v_bkt_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v_size_x27_1187_; lean_object* v___x_1188_; lean_object* v_buckets_x27_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1186_ = lean_unsigned_to_nat(1u);
v_size_x27_1187_ = lean_nat_add(v_size_1166_, v___x_1186_);
lean_dec(v_size_1166_);
lean_inc(v_bkt_1184_);
v___x_1188_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1188_, 0, v_a_1164_);
lean_ctor_set(v___x_1188_, 1, v_b_1165_);
lean_ctor_set(v___x_1188_, 2, v_bkt_1184_);
v_buckets_x27_1189_ = lean_array_uset(v_buckets_1167_, v___x_1183_, v___x_1188_);
v___x_1190_ = lean_unsigned_to_nat(4u);
v___x_1191_ = lean_nat_mul(v_size_x27_1187_, v___x_1190_);
v___x_1192_ = lean_unsigned_to_nat(3u);
v___x_1193_ = lean_nat_div(v___x_1191_, v___x_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_array_get_size(v_buckets_x27_1189_);
v___x_1195_ = lean_nat_dec_le(v___x_1193_, v___x_1194_);
lean_dec(v___x_1193_);
if (v___x_1195_ == 0)
{
lean_object* v_val_1196_; lean_object* v___x_1198_; 
v_val_1196_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11___redArg(v_buckets_x27_1189_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v_val_1196_);
lean_ctor_set(v___x_1169_, 0, v_size_x27_1187_);
v___x_1198_ = v___x_1169_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_size_x27_1187_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_val_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
else
{
lean_object* v___x_1201_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v_buckets_x27_1189_);
lean_ctor_set(v___x_1169_, 0, v_size_x27_1187_);
v___x_1201_ = v___x_1169_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_size_x27_1187_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_buckets_x27_1189_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
else
{
lean_object* v___x_1203_; lean_object* v_buckets_x27_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1208_; 
lean_inc(v_bkt_1184_);
v___x_1203_ = lean_box(0);
v_buckets_x27_1204_ = lean_array_uset(v_buckets_1167_, v___x_1183_, v___x_1203_);
v___x_1205_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(v_a_1164_, v_b_1165_, v_bkt_1184_);
v___x_1206_ = lean_array_uset(v_buckets_x27_1204_, v___x_1183_, v___x_1205_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1206_);
v___x_1208_ = v___x_1169_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_size_1166_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1(lean_object* v_a_1211_, lean_object* v_e_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1215_ = lean_st_ref_take(v_a_1211_);
v___x_1216_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(v___x_1215_, v_e_1212_, v_a_1213_);
v___x_1217_ = lean_st_ref_put(v_a_1211_, v___x_1216_);
v___x_1218_ = lean_box(0);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_a_1219_, lean_object* v_e_1220_, lean_object* v_a_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1(v_a_1219_, v_e_1220_, v_a_1221_);
lean_dec(v_a_1219_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(lean_object* v_name_1224_, lean_object* v_type_1225_, lean_object* v_val_1226_, lean_object* v_k_1227_, uint8_t v_nondep_1228_, uint8_t v_kind_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v___f_1236_; lean_object* v___x_1237_; 
lean_inc(v___y_1230_);
v___f_1236_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1236_, 0, v_k_1227_);
lean_closure_set(v___f_1236_, 1, v___y_1230_);
v___x_1237_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1224_, v_type_1225_, v_val_1226_, v___f_1236_, v_nondep_1228_, v_kind_1229_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
if (lean_obj_tag(v___x_1237_) == 0)
{
return v___x_1237_;
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1237_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1237_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg___boxed(lean_object* v_name_1246_, lean_object* v_type_1247_, lean_object* v_val_1248_, lean_object* v_k_1249_, lean_object* v_nondep_1250_, lean_object* v_kind_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
uint8_t v_nondep_boxed_1258_; uint8_t v_kind_boxed_1259_; lean_object* v_res_1260_; 
v_nondep_boxed_1258_ = lean_unbox(v_nondep_1250_);
v_kind_boxed_1259_ = lean_unbox(v_kind_1251_);
v_res_1260_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(v_name_1246_, v_type_1247_, v_val_1248_, v_k_1249_, v_nondep_boxed_1258_, v_kind_boxed_1259_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0___boxed(lean_object* v_fvars_1261_, lean_object* v_f_1262_, lean_object* v_body_1263_, lean_object* v_x_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0(v_fvars_1261_, v_f_1262_, v_body_1263_, v_x_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(lean_object* v_f_1272_, lean_object* v_fvars_1273_, lean_object* v_a_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
if (lean_obj_tag(v_a_1274_) == 8)
{
lean_object* v_declName_1281_; lean_object* v_type_1282_; lean_object* v_value_1283_; lean_object* v_body_1284_; lean_object* v_d_1285_; lean_object* v___x_1286_; 
v_declName_1281_ = lean_ctor_get(v_a_1274_, 0);
lean_inc(v_declName_1281_);
v_type_1282_ = lean_ctor_get(v_a_1274_, 1);
lean_inc_ref(v_type_1282_);
v_value_1283_ = lean_ctor_get(v_a_1274_, 2);
lean_inc_ref(v_value_1283_);
v_body_1284_ = lean_ctor_get(v_a_1274_, 3);
lean_inc_ref(v_body_1284_);
lean_dec_ref_known(v_a_1274_, 4);
v_d_1285_ = lean_expr_instantiate_rev(v_type_1282_, v_fvars_1273_);
lean_dec_ref(v_type_1282_);
lean_inc_ref(v_f_1272_);
lean_inc(v___y_1279_);
lean_inc_ref(v___y_1278_);
lean_inc(v___y_1277_);
lean_inc_ref(v___y_1276_);
lean_inc(v___y_1275_);
lean_inc_ref(v_d_1285_);
v___x_1286_ = lean_apply_7(v_f_1272_, v_d_1285_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, lean_box(0));
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_v_1287_; lean_object* v___x_1288_; 
lean_dec_ref_known(v___x_1286_, 1);
v_v_1287_ = lean_expr_instantiate_rev(v_value_1283_, v_fvars_1273_);
lean_dec_ref(v_value_1283_);
lean_inc_ref(v_f_1272_);
lean_inc(v___y_1279_);
lean_inc_ref(v___y_1278_);
lean_inc(v___y_1277_);
lean_inc_ref(v___y_1276_);
lean_inc(v___y_1275_);
lean_inc_ref(v_v_1287_);
v___x_1288_ = lean_apply_7(v_f_1272_, v_v_1287_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, lean_box(0));
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v___f_1289_; uint8_t v___x_1290_; uint8_t v___x_1291_; lean_object* v___x_1292_; 
lean_dec_ref_known(v___x_1288_, 1);
v___f_1289_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1289_, 0, v_fvars_1273_);
lean_closure_set(v___f_1289_, 1, v_f_1272_);
lean_closure_set(v___f_1289_, 2, v_body_1284_);
v___x_1290_ = 0;
v___x_1291_ = 0;
v___x_1292_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(v_declName_1281_, v_d_1285_, v_v_1287_, v___f_1289_, v___x_1290_, v___x_1291_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1292_;
}
else
{
lean_dec_ref(v_v_1287_);
lean_dec_ref(v_d_1285_);
lean_dec_ref(v_body_1284_);
lean_dec(v_declName_1281_);
lean_dec_ref(v_fvars_1273_);
lean_dec_ref(v_f_1272_);
return v___x_1288_;
}
}
else
{
lean_dec_ref(v_d_1285_);
lean_dec_ref(v_body_1284_);
lean_dec_ref(v_value_1283_);
lean_dec(v_declName_1281_);
lean_dec_ref(v_fvars_1273_);
lean_dec_ref(v_f_1272_);
return v___x_1286_;
}
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = lean_expr_instantiate_rev(v_a_1274_, v_fvars_1273_);
lean_dec_ref(v_fvars_1273_);
lean_dec_ref(v_a_1274_);
lean_inc(v___y_1279_);
lean_inc_ref(v___y_1278_);
lean_inc(v___y_1277_);
lean_inc_ref(v___y_1276_);
lean_inc(v___y_1275_);
v___x_1294_ = lean_apply_7(v_f_1272_, v___x_1293_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, lean_box(0));
return v___x_1294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0(lean_object* v_fvars_1295_, lean_object* v_f_1296_, lean_object* v_body_1297_, lean_object* v_x_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_array_push(v_fvars_1295_, v_x_1298_);
v___x_1306_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(v_f_1296_, v___x_1305_, v_body_1297_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___boxed(lean_object* v_f_1307_, lean_object* v_fvars_1308_, lean_object* v_a_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(v_f_1307_, v_fvars_1308_, v_a_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(lean_object* v_f_1317_, lean_object* v_e_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_1326_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(v_f_1317_, v___x_1325_, v_e_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11___boxed(lean_object* v_f_1327_, lean_object* v_e_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(v_f_1327_, v_e_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed(lean_object* v_fn_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2(v_fn_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(lean_object* v_fn_1345_, lean_object* v_e_1346_, lean_object* v_a_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_a_1354_; lean_object* v___y_1366_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_inc(v_a_1347_);
v___x_1368_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1368_, 0, lean_box(0));
lean_closure_set(v___x_1368_, 1, lean_box(0));
lean_closure_set(v___x_1368_, 2, v_a_1347_);
v___x_1369_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_box(0), v___x_1368_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1406_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1372_ = v___x_1369_;
v_isShared_1373_ = v_isSharedCheck_1406_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1369_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1406_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_a_1370_, v_e_1346_);
lean_dec(v_a_1370_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v___x_1375_; 
lean_del_object(v___x_1372_);
lean_inc_ref(v_fn_1345_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
lean_inc_ref(v_e_1346_);
v___x_1375_ = lean_apply_6(v_fn_1345_, v_e_1346_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, lean_box(0));
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; uint8_t v___x_1377_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1377_ = lean_unbox(v_a_1376_);
lean_dec(v_a_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; 
lean_dec_ref(v_fn_1345_);
v___x_1378_ = lean_box(0);
v_a_1354_ = v___x_1378_;
goto v___jp_1353_;
}
else
{
switch(lean_obj_tag(v_e_1346_))
{
case 7:
{
lean_object* v___f_1379_; lean_object* v___x_1380_; 
v___f_1379_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1379_, 0, v_fn_1345_);
lean_inc_ref(v_e_1346_);
v___x_1380_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(v___f_1379_, v_e_1346_, v_a_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
v___y_1366_ = v___x_1380_;
goto v___jp_1365_;
}
case 6:
{
lean_object* v___f_1381_; lean_object* v___x_1382_; 
v___f_1381_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1381_, 0, v_fn_1345_);
lean_inc_ref(v_e_1346_);
v___x_1382_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(v___f_1381_, v_e_1346_, v_a_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
v___y_1366_ = v___x_1382_;
goto v___jp_1365_;
}
case 8:
{
lean_object* v___f_1383_; lean_object* v___x_1384_; 
v___f_1383_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1383_, 0, v_fn_1345_);
lean_inc_ref(v_e_1346_);
v___x_1384_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(v___f_1383_, v_e_1346_, v_a_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
v___y_1366_ = v___x_1384_;
goto v___jp_1365_;
}
case 5:
{
lean_object* v_fn_1385_; lean_object* v_arg_1386_; lean_object* v___x_1387_; 
v_fn_1385_ = lean_ctor_get(v_e_1346_, 0);
v_arg_1386_ = lean_ctor_get(v_e_1346_, 1);
lean_inc_ref(v_fn_1385_);
lean_inc_ref(v_fn_1345_);
v___x_1387_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1345_, v_fn_1385_, v_a_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v___x_1388_; 
lean_dec_ref_known(v___x_1387_, 1);
lean_inc_ref(v_arg_1386_);
v___x_1388_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1345_, v_arg_1386_, v_a_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
v___y_1366_ = v___x_1388_;
goto v___jp_1365_;
}
else
{
lean_dec_ref(v_fn_1345_);
v___y_1366_ = v___x_1387_;
goto v___jp_1365_;
}
}
case 10:
{
lean_object* v_expr_1389_; lean_object* v___x_1390_; 
v_expr_1389_ = lean_ctor_get(v_e_1346_, 1);
lean_inc_ref(v_expr_1389_);
v___x_1390_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1345_, v_expr_1389_, v_a_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
v___y_1366_ = v___x_1390_;
goto v___jp_1365_;
}
case 11:
{
lean_object* v_struct_1391_; lean_object* v___x_1392_; 
v_struct_1391_ = lean_ctor_get(v_e_1346_, 2);
lean_inc_ref(v_struct_1391_);
v___x_1392_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1345_, v_struct_1391_, v_a_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
v___y_1366_ = v___x_1392_;
goto v___jp_1365_;
}
default: 
{
lean_object* v___x_1393_; 
lean_dec_ref(v_fn_1345_);
v___x_1393_ = lean_box(0);
v_a_1354_ = v___x_1393_;
goto v___jp_1353_;
}
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec_ref(v_e_1346_);
lean_dec_ref(v_fn_1345_);
v_a_1394_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1375_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1375_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
else
{
lean_object* v_val_1402_; lean_object* v___x_1404_; 
lean_dec_ref(v_e_1346_);
lean_dec_ref(v_fn_1345_);
v_val_1402_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_val_1402_);
lean_dec_ref_known(v___x_1374_, 1);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v_val_1402_);
v___x_1404_ = v___x_1372_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_val_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec_ref(v_e_1346_);
lean_dec_ref(v_fn_1345_);
v_a_1407_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1369_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1369_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
v___jp_1353_:
{
lean_object* v___f_1355_; lean_object* v___x_1356_; 
lean_inc(v_a_1347_);
v___f_1355_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1355_, 0, v_a_1347_);
lean_closure_set(v___f_1355_, 1, v_e_1346_);
lean_closure_set(v___f_1355_, 2, v_a_1354_);
v___x_1356_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_box(0), v___f_1355_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1363_ == 0)
{
lean_object* v_unused_1364_; 
v_unused_1364_ = lean_ctor_get(v___x_1356_, 0);
lean_dec(v_unused_1364_);
v___x_1358_ = v___x_1356_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_dec(v___x_1356_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v_a_1354_);
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1354_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
else
{
return v___x_1356_;
}
}
v___jp_1365_:
{
if (lean_obj_tag(v___y_1366_) == 0)
{
lean_object* v_a_1367_; 
v_a_1367_ = lean_ctor_get(v___y_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___y_1366_, 1);
v_a_1354_ = v_a_1367_;
goto v___jp_1353_;
}
else
{
lean_dec_ref(v_e_1346_);
return v___y_1366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2(lean_object* v_fn_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___boxed(lean_object* v_fn_1424_, lean_object* v_e_1425_, lean_object* v_a_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1424_, v_e_1425_, v_a_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v_a_1426_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_object* v_00_u03b1_1433_, lean_object* v_x_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = lean_apply_1(v_x_1434_, lean_box(0));
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0___boxed(lean_object* v_00_u03b1_1442_, lean_object* v_x_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(v_00_u03b1_1442_, v_x_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(lean_object* v_input_1450_, lean_object* v_fn_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v_a_1459_; lean_object* v___x_1460_; 
v___x_1457_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___redArg___closed__2, &l_Lean_Meta_forEachExpr_x27___redArg___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__2);
v___x_1458_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_box(0), v___x_1457_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
lean_inc(v_a_1459_);
lean_dec_ref(v___x_1458_);
v___x_1460_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1451_, v_input_1450_, v_a_1459_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
v___x_1462_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1462_, 0, lean_box(0));
lean_closure_set(v___x_1462_, 1, lean_box(0));
lean_closure_set(v___x_1462_, 2, v_a_1459_);
v___x_1463_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_box(0), v___x_1462_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v___x_1463_, 0);
lean_dec(v_unused_1471_);
v___x_1465_ = v___x_1463_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_dec(v___x_1463_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v_a_1461_);
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1461_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
else
{
lean_dec(v_a_1459_);
return v___x_1460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___boxed(lean_object* v_input_1472_, lean_object* v_fn_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(v_input_1472_, v_fn_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0(lean_object* v_f_1480_, lean_object* v_e_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___x_1487_; 
lean_inc(v___y_1485_);
lean_inc_ref(v___y_1484_);
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1482_);
v___x_1487_ = lean_apply_6(v_f_1480_, v_e_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, lean_box(0));
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1496_; 
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; 
v_unused_1497_ = lean_ctor_get(v___x_1487_, 0);
lean_dec(v_unused_1497_);
v___x_1489_ = v___x_1487_;
v_isShared_1490_ = v_isSharedCheck_1496_;
goto v_resetjp_1488_;
}
else
{
lean_dec(v___x_1487_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1496_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
uint8_t v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1491_ = 1;
v___x_1492_ = lean_box(v___x_1491_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v___x_1492_);
v___x_1494_ = v___x_1489_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
v_a_1498_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1487_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1487_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0___boxed(lean_object* v_f_1506_, lean_object* v_e_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0(v_f_1506_, v_e_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(lean_object* v_e_1514_, lean_object* v_f_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___f_1521_; lean_object* v___x_1522_; 
v___f_1521_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1521_, 0, v_f_1515_);
v___x_1522_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(v_e_1514_, v___f_1521_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___boxed(lean_object* v_e_1523_, lean_object* v_f_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(v_e_1523_, v_f_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt(lean_object* v_e_1533_, lean_object* v_isTarget_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v_a_1544_; lean_object* v___f_1545_; lean_object* v___x_1546_; 
v___x_1540_ = lean_unsigned_to_nat(0u);
v___x_1541_ = ((lean_object*)(l_Lean_Meta_setMVarUserNamesAt___closed__0));
v___x_1542_ = lean_st_mk_ref(v___x_1541_);
v___x_1543_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(v_e_1533_, v_a_1536_);
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
lean_dec_ref(v___x_1543_);
lean_inc(v___x_1542_);
v___f_1545_ = lean_alloc_closure((void*)(l_Lean_Meta_setMVarUserNamesAt___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1545_, 0, v___x_1542_);
lean_closure_set(v___f_1545_, 1, v_isTarget_1534_);
lean_closure_set(v___f_1545_, 2, v___x_1540_);
v___x_1546_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(v_a_1544_, v___f_1545_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1554_; 
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; 
v_unused_1555_ = lean_ctor_get(v___x_1546_, 0);
lean_dec(v_unused_1555_);
v___x_1548_ = v___x_1546_;
v_isShared_1549_ = v_isSharedCheck_1554_;
goto v_resetjp_1547_;
}
else
{
lean_dec(v___x_1546_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1554_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v___x_1552_; 
v___x_1550_ = lean_st_ref_get(v___x_1542_);
lean_dec(v___x_1542_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v___x_1550_);
v___x_1552_ = v___x_1548_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v___x_1542_);
v_a_1556_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1546_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1546_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___boxed(lean_object* v_e_1564_, lean_object* v_isTarget_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_Meta_setMVarUserNamesAt(v_e_1564_, v_isTarget_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2(lean_object* v_upperBound_1572_, lean_object* v___x_1573_, lean_object* v_val_1574_, lean_object* v_e_1575_, lean_object* v_isTarget_1576_, lean_object* v_inst_1577_, lean_object* v_R_1578_, lean_object* v_a_1579_, lean_object* v_b_1580_, lean_object* v_c_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(v_upperBound_1572_, v___x_1573_, v_val_1574_, v_e_1575_, v_isTarget_1576_, v_a_1579_, v_b_1580_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___boxed(lean_object* v_upperBound_1588_, lean_object* v___x_1589_, lean_object* v_val_1590_, lean_object* v_e_1591_, lean_object* v_isTarget_1592_, lean_object* v_inst_1593_, lean_object* v_R_1594_, lean_object* v_a_1595_, lean_object* v_b_1596_, lean_object* v_c_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2(v_upperBound_1588_, v___x_1589_, v_val_1590_, v_e_1591_, v_isTarget_1592_, v_inst_1593_, v_R_1594_, v_a_1595_, v_b_1596_, v_c_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec_ref(v_isTarget_1592_);
lean_dec_ref(v_e_1591_);
lean_dec_ref(v___x_1589_);
lean_dec(v_upperBound_1588_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_1604_, lean_object* v_m_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_m_1605_, v_a_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___boxed(lean_object* v_00_u03b2_1608_, lean_object* v_m_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7(v_00_u03b2_1608_, v_m_1609_, v_a_1610_);
lean_dec_ref(v_a_1610_);
lean_dec_ref(v_m_1609_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_1612_, lean_object* v_m_1613_, lean_object* v_a_1614_, lean_object* v_b_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(v_m_1613_, v_a_1614_, v_b_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_1617_, lean_object* v_a_1618_, lean_object* v_x_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(v_a_1618_, v_x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03b2_1621_, lean_object* v_a_1622_, lean_object* v_x_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8(v_00_u03b2_1621_, v_a_1622_, v_x_1623_);
lean_dec(v_x_1623_);
lean_dec_ref(v_a_1622_);
return v_res_1624_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_1625_, lean_object* v_a_1626_, lean_object* v_x_1627_){
_start:
{
uint8_t v___x_1628_; 
v___x_1628_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_a_1626_, v_x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b2_1629_, lean_object* v_a_1630_, lean_object* v_x_1631_){
_start:
{
uint8_t v_res_1632_; lean_object* v_r_1633_; 
v_res_1632_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10(v_00_u03b2_1629_, v_a_1630_, v_x_1631_);
lean_dec(v_x_1631_);
lean_dec_ref(v_a_1630_);
v_r_1633_ = lean_box(v_res_1632_);
return v_r_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11(lean_object* v_00_u03b2_1634_, lean_object* v_data_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11___redArg(v_data_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12(lean_object* v_00_u03b2_1637_, lean_object* v_a_1638_, lean_object* v_b_1639_, lean_object* v_x_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(v_a_1638_, v_b_1639_, v_x_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16(lean_object* v_00_u03b1_1642_, lean_object* v_name_1643_, uint8_t v_bi_1644_, lean_object* v_type_1645_, lean_object* v_k_1646_, uint8_t v_kind_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_name_1643_, v_bi_1644_, v_type_1645_, v_k_1646_, v_kind_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1655_, lean_object* v_name_1656_, lean_object* v_bi_1657_, lean_object* v_type_1658_, lean_object* v_k_1659_, lean_object* v_kind_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
uint8_t v_bi_boxed_1667_; uint8_t v_kind_boxed_1668_; lean_object* v_res_1669_; 
v_bi_boxed_1667_ = lean_unbox(v_bi_1657_);
v_kind_boxed_1668_ = lean_unbox(v_kind_1660_);
v_res_1669_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16(v_00_u03b1_1655_, v_name_1656_, v_bi_boxed_1667_, v_type_1658_, v_k_1659_, v_kind_boxed_1668_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21(lean_object* v_00_u03b1_1670_, lean_object* v_name_1671_, lean_object* v_type_1672_, lean_object* v_val_1673_, lean_object* v_k_1674_, uint8_t v_nondep_1675_, uint8_t v_kind_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(v_name_1671_, v_type_1672_, v_val_1673_, v_k_1674_, v_nondep_1675_, v_kind_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___boxed(lean_object* v_00_u03b1_1684_, lean_object* v_name_1685_, lean_object* v_type_1686_, lean_object* v_val_1687_, lean_object* v_k_1688_, lean_object* v_nondep_1689_, lean_object* v_kind_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
uint8_t v_nondep_boxed_1697_; uint8_t v_kind_boxed_1698_; lean_object* v_res_1699_; 
v_nondep_boxed_1697_ = lean_unbox(v_nondep_1689_);
v_kind_boxed_1698_ = lean_unbox(v_kind_1690_);
v_res_1699_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21(v_00_u03b1_1684_, v_name_1685_, v_type_1686_, v_val_1687_, v_k_1688_, v_nondep_boxed_1697_, v_kind_boxed_1698_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_1700_, lean_object* v_i_1701_, lean_object* v_source_1702_, lean_object* v_target_1703_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12___redArg(v_i_1701_, v_source_1702_, v_target_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16(lean_object* v_00_u03b2_1705_, lean_object* v_x_1706_, lean_object* v_x_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16___redArg(v_x_1706_, v_x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(lean_object* v_as_1709_, size_t v_sz_1710_, size_t v_i_1711_, lean_object* v_b_1712_, lean_object* v___y_1713_){
_start:
{
uint8_t v___x_1715_; 
v___x_1715_ = lean_usize_dec_lt(v_i_1711_, v_sz_1710_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1716_, 0, v_b_1712_);
return v___x_1716_;
}
else
{
lean_object* v___x_1717_; lean_object* v_mctx_1718_; lean_object* v_cache_1719_; lean_object* v_zetaDeltaFVarIds_1720_; lean_object* v_postponed_1721_; lean_object* v_diag_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1737_; 
v___x_1717_ = lean_st_ref_take(v___y_1713_);
v_mctx_1718_ = lean_ctor_get(v___x_1717_, 0);
v_cache_1719_ = lean_ctor_get(v___x_1717_, 1);
v_zetaDeltaFVarIds_1720_ = lean_ctor_get(v___x_1717_, 2);
v_postponed_1721_ = lean_ctor_get(v___x_1717_, 3);
v_diag_1722_ = lean_ctor_get(v___x_1717_, 4);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1724_ = v___x_1717_;
v_isShared_1725_ = v_isSharedCheck_1737_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_diag_1722_);
lean_inc(v_postponed_1721_);
lean_inc(v_zetaDeltaFVarIds_1720_);
lean_inc(v_cache_1719_);
lean_inc(v_mctx_1718_);
lean_dec(v___x_1717_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1737_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v_a_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1730_; 
v_a_1726_ = lean_array_uget_borrowed(v_as_1709_, v_i_1711_);
v___x_1727_ = lean_box(0);
lean_inc(v_a_1726_);
v___x_1728_ = l_Lean_MetavarContext_setMVarUserNameTemporarily(v_mctx_1718_, v_a_1726_, v___x_1727_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1728_);
v___x_1730_ = v___x_1724_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_cache_1719_);
lean_ctor_set(v_reuseFailAlloc_1736_, 2, v_zetaDeltaFVarIds_1720_);
lean_ctor_set(v_reuseFailAlloc_1736_, 3, v_postponed_1721_);
lean_ctor_set(v_reuseFailAlloc_1736_, 4, v_diag_1722_);
v___x_1730_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; size_t v___x_1733_; size_t v___x_1734_; 
v___x_1731_ = lean_st_ref_put(v___y_1713_, v___x_1730_);
v___x_1732_ = lean_box(0);
v___x_1733_ = ((size_t)1ULL);
v___x_1734_ = lean_usize_add(v_i_1711_, v___x_1733_);
v_i_1711_ = v___x_1734_;
v_b_1712_ = v___x_1732_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg___boxed(lean_object* v_as_1738_, lean_object* v_sz_1739_, lean_object* v_i_1740_, lean_object* v_b_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
size_t v_sz_boxed_1744_; size_t v_i_boxed_1745_; lean_object* v_res_1746_; 
v_sz_boxed_1744_ = lean_unbox_usize(v_sz_1739_);
lean_dec(v_sz_1739_);
v_i_boxed_1745_ = lean_unbox_usize(v_i_1740_);
lean_dec(v_i_1740_);
v_res_1746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_as_1738_, v_sz_boxed_1744_, v_i_boxed_1745_, v_b_1741_, v___y_1742_);
lean_dec(v___y_1742_);
lean_dec_ref(v_as_1738_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_resetMVarUserNames(lean_object* v_toReset_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v___x_1753_; size_t v_sz_1754_; size_t v___x_1755_; lean_object* v___x_1756_; 
v___x_1753_ = lean_box(0);
v_sz_1754_ = lean_array_size(v_toReset_1747_);
v___x_1755_ = ((size_t)0ULL);
v___x_1756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_toReset_1747_, v_sz_1754_, v___x_1755_, v___x_1753_, v_a_1749_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1763_ == 0)
{
lean_object* v_unused_1764_; 
v_unused_1764_ = lean_ctor_get(v___x_1756_, 0);
lean_dec(v_unused_1764_);
v___x_1758_ = v___x_1756_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_dec(v___x_1756_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1753_);
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1753_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
else
{
return v___x_1756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_resetMVarUserNames___boxed(lean_object* v_toReset_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_Meta_resetMVarUserNames(v_toReset_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
lean_dec(v_a_1769_);
lean_dec_ref(v_a_1768_);
lean_dec(v_a_1767_);
lean_dec_ref(v_a_1766_);
lean_dec_ref(v_toReset_1765_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0(lean_object* v_as_1772_, size_t v_sz_1773_, size_t v_i_1774_, lean_object* v_b_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_as_1772_, v_sz_1773_, v_i_1774_, v_b_1775_, v___y_1777_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___boxed(lean_object* v_as_1782_, lean_object* v_sz_1783_, lean_object* v_i_1784_, lean_object* v_b_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
size_t v_sz_boxed_1791_; size_t v_i_boxed_1792_; lean_object* v_res_1793_; 
v_sz_boxed_1791_ = lean_unbox_usize(v_sz_1783_);
lean_dec(v_sz_1783_);
v_i_boxed_1792_ = lean_unbox_usize(v_i_1784_);
lean_dec(v_i_1784_);
v_res_1793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0(v_as_1782_, v_sz_boxed_1791_, v_i_boxed_1792_, v_b_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec_ref(v_as_1782_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(lean_object* v_x_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
if (lean_obj_tag(v_x_1794_) == 2)
{
lean_object* v_mvarId_1800_; lean_object* v___x_1801_; 
v_mvarId_1800_ = lean_ctor_get(v_x_1794_, 0);
lean_inc(v_mvarId_1800_);
lean_dec_ref_known(v_x_1794_, 1);
v___x_1801_ = l_Lean_MVarId_getDecl(v_mvarId_1800_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1812_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1812_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1812_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v_userName_1806_; uint8_t v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1810_; 
v_userName_1806_ = lean_ctor_get(v_a_1802_, 0);
lean_inc(v_userName_1806_);
lean_dec(v_a_1802_);
v___x_1807_ = l_Lean_Name_isAnonymous(v_userName_1806_);
lean_dec(v_userName_1806_);
v___x_1808_ = lean_box(v___x_1807_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1808_);
v___x_1810_ = v___x_1804_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
v_a_1813_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1801_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1801_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
else
{
uint8_t v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_dec_ref(v_x_1794_);
v___x_1821_ = 0;
v___x_1822_ = lean_box(v___x_1821_);
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
return v___x_1823_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0___boxed(lean_object* v_x_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(v_x_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__0(lean_object* v_val_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_x3f_1836_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = lean_st_ref_get(v_val_1831_);
v___x_1839_ = l_Lean_Meta_resetMVarUserNames(v___x_1838_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_);
lean_dec(v___x_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__0___boxed(lean_object* v_val_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_x3f_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_Meta_mkForallFVars_x27___lam__0(v_val_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_x3f_1845_);
lean_dec(v_a_x3f_1845_);
lean_dec(v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_val_1840_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(lean_object* v_xs_1848_, lean_object* v_as_1849_, size_t v_sz_1850_, size_t v_i_1851_, lean_object* v_b_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
uint8_t v___x_1859_; 
v___x_1859_ = lean_usize_dec_lt(v_i_1851_, v_sz_1850_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; 
lean_dec_ref(v_xs_1848_);
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v_b_1852_);
return v___x_1860_;
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1862_; 
v_a_1861_ = lean_array_uget_borrowed(v_as_1849_, v_i_1851_);
lean_inc(v___y_1857_);
lean_inc_ref(v___y_1856_);
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
lean_inc(v_a_1861_);
v___x_1862_ = lean_infer_type(v_a_1861_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1864_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1863_);
lean_dec_ref_known(v___x_1862_, 1);
lean_inc_ref(v_xs_1848_);
v___x_1864_ = l_Lean_Meta_setMVarUserNamesAt(v_a_1863_, v_xs_1848_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; size_t v___x_1870_; size_t v___x_1871_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref_known(v___x_1864_, 1);
v___x_1866_ = lean_st_ref_take(v___y_1853_);
v___x_1867_ = l_Array_append___redArg(v___x_1866_, v_a_1865_);
lean_dec(v_a_1865_);
v___x_1868_ = lean_st_ref_put(v___y_1853_, v___x_1867_);
v___x_1869_ = lean_box(0);
v___x_1870_ = ((size_t)1ULL);
v___x_1871_ = lean_usize_add(v_i_1851_, v___x_1870_);
v_i_1851_ = v___x_1871_;
v_b_1852_ = v___x_1869_;
goto _start;
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec_ref(v_xs_1848_);
v_a_1873_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1864_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1864_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec_ref(v_xs_1848_);
v_a_1881_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1862_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1862_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2___boxed(lean_object* v_xs_1889_, lean_object* v_as_1890_, lean_object* v_sz_1891_, lean_object* v_i_1892_, lean_object* v_b_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
size_t v_sz_boxed_1900_; size_t v_i_boxed_1901_; lean_object* v_res_1902_; 
v_sz_boxed_1900_ = lean_unbox_usize(v_sz_1891_);
lean_dec(v_sz_1891_);
v_i_boxed_1901_ = lean_unbox_usize(v_i_1892_);
lean_dec(v_i_1892_);
v_res_1902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(v_xs_1889_, v_as_1890_, v_sz_boxed_1900_, v_i_boxed_1901_, v_b_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
lean_dec(v___y_1894_);
lean_dec_ref(v_as_1890_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(lean_object* v_xs_1903_, lean_object* v_as_1904_, size_t v_sz_1905_, size_t v_i_1906_, lean_object* v_b_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
uint8_t v___x_1914_; 
v___x_1914_ = lean_usize_dec_lt(v_i_1906_, v_sz_1905_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; 
lean_dec_ref(v_xs_1903_);
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v_b_1907_);
return v___x_1915_;
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1917_; 
v_a_1916_ = lean_array_uget_borrowed(v_as_1904_, v_i_1906_);
lean_inc(v___y_1912_);
lean_inc_ref(v___y_1911_);
lean_inc(v___y_1910_);
lean_inc_ref(v___y_1909_);
lean_inc(v_a_1916_);
v___x_1917_ = lean_infer_type(v_a_1916_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1919_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
lean_inc_ref(v_xs_1903_);
v___x_1919_ = l_Lean_Meta_setMVarUserNamesAt(v_a_1918_, v_xs_1903_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; size_t v___x_1925_; size_t v___x_1926_; lean_object* v___x_1927_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v___x_1921_ = lean_st_ref_take(v___y_1908_);
v___x_1922_ = l_Array_append___redArg(v___x_1921_, v_a_1920_);
lean_dec(v_a_1920_);
v___x_1923_ = lean_st_ref_put(v___y_1908_, v___x_1922_);
v___x_1924_ = lean_box(0);
v___x_1925_ = ((size_t)1ULL);
v___x_1926_ = lean_usize_add(v_i_1906_, v___x_1925_);
v___x_1927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(v_xs_1903_, v_as_1904_, v_sz_1905_, v___x_1926_, v___x_1924_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
return v___x_1927_;
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec_ref(v_xs_1903_);
v_a_1928_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1919_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1919_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec_ref(v_xs_1903_);
v_a_1936_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1917_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1917_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2___boxed(lean_object* v_xs_1944_, lean_object* v_as_1945_, lean_object* v_sz_1946_, lean_object* v_i_1947_, lean_object* v_b_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
size_t v_sz_boxed_1955_; size_t v_i_boxed_1956_; lean_object* v_res_1957_; 
v_sz_boxed_1955_ = lean_unbox_usize(v_sz_1946_);
lean_dec(v_sz_1946_);
v_i_boxed_1956_ = lean_unbox_usize(v_i_1947_);
lean_dec(v_i_1947_);
v_res_1957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(v_xs_1944_, v_as_1945_, v_sz_boxed_1955_, v_i_boxed_1956_, v_b_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v_as_1945_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(lean_object* v_as_1958_, size_t v_i_1959_, size_t v_stop_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
uint8_t v___x_1966_; 
v___x_1966_ = lean_usize_dec_eq(v_i_1959_, v_stop_1960_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = lean_array_uget_borrowed(v_as_1958_, v_i_1959_);
lean_inc(v___x_1967_);
v___x_1968_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(v___x_1967_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1980_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_1980_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1980_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
uint8_t v___x_1973_; 
v___x_1973_ = lean_unbox(v_a_1969_);
if (v___x_1973_ == 0)
{
size_t v___x_1974_; size_t v___x_1975_; 
lean_del_object(v___x_1971_);
lean_dec(v_a_1969_);
v___x_1974_ = ((size_t)1ULL);
v___x_1975_ = lean_usize_add(v_i_1959_, v___x_1974_);
v_i_1959_ = v___x_1975_;
goto _start;
}
else
{
lean_object* v___x_1978_; 
if (v_isShared_1972_ == 0)
{
v___x_1978_ = v___x_1971_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1969_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
else
{
return v___x_1968_;
}
}
else
{
uint8_t v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1981_ = 0;
v___x_1982_ = lean_box(v___x_1981_);
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
return v___x_1983_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1___boxed(lean_object* v_as_1984_, lean_object* v_i_1985_, lean_object* v_stop_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
size_t v_i_boxed_1992_; size_t v_stop_boxed_1993_; lean_object* v_res_1994_; 
v_i_boxed_1992_ = lean_unbox_usize(v_i_1985_);
lean_dec(v_i_1985_);
v_stop_boxed_1993_ = lean_unbox_usize(v_stop_1986_);
lean_dec(v_stop_1986_);
v_res_1994_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(v_as_1984_, v_i_boxed_1992_, v_stop_boxed_1993_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
lean_dec(v___y_1990_);
lean_dec_ref(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec_ref(v_as_1984_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27(lean_object* v_xs_1995_, lean_object* v_type_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
uint8_t v_a_2003_; lean_object* v___x_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v___x_2007_ = lean_unsigned_to_nat(0u);
v___x_2008_ = lean_array_get_size(v_xs_1995_);
v___x_2009_ = lean_nat_dec_lt(v___x_2007_, v___x_2008_);
if (v___x_2009_ == 0)
{
v_a_2003_ = v___x_2009_;
goto v___jp_2002_;
}
else
{
if (v___x_2009_ == 0)
{
v_a_2003_ = v___x_2009_;
goto v___jp_2002_;
}
else
{
size_t v___x_2010_; size_t v___x_2011_; lean_object* v___x_2012_; 
v___x_2010_ = ((size_t)0ULL);
v___x_2011_ = lean_usize_of_nat(v___x_2008_);
v___x_2012_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(v_xs_1995_, v___x_2010_, v___x_2011_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; uint8_t v___x_2014_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_2012_, 1);
v___x_2014_ = lean_unbox(v_a_2013_);
if (v___x_2014_ == 0)
{
uint8_t v___x_2015_; 
v___x_2015_ = lean_unbox(v_a_2013_);
lean_dec(v_a_2013_);
v_a_2003_ = v___x_2015_;
goto v___jp_2002_;
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v_a_2019_; lean_object* v___x_2038_; size_t v_sz_2039_; lean_object* v___x_2040_; 
lean_dec(v_a_2013_);
v___x_2016_ = ((lean_object*)(l_Lean_Meta_setMVarUserNamesAt___closed__0));
v___x_2017_ = lean_st_mk_ref(v___x_2016_);
v___x_2038_ = lean_box(0);
v_sz_2039_ = lean_array_size(v_xs_1995_);
lean_inc_ref(v_xs_1995_);
v___x_2040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(v_xs_1995_, v_xs_1995_, v_sz_2039_, v___x_2010_, v___x_2038_, v___x_2017_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v___x_2041_; 
lean_dec_ref_known(v___x_2040_, 1);
lean_inc_ref(v_xs_1995_);
lean_inc_ref(v_type_1996_);
v___x_2041_ = l_Lean_Meta_setMVarUserNamesAt(v_type_1996_, v_xs_1995_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; uint8_t v___x_2047_; lean_object* v___x_2048_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v___x_2043_ = lean_st_ref_take(v___x_2017_);
v___x_2044_ = l_Array_append___redArg(v___x_2043_, v_a_2042_);
lean_dec(v_a_2042_);
v___x_2045_ = lean_st_ref_put(v___x_2017_, v___x_2044_);
v___x_2046_ = 0;
v___x_2047_ = 1;
v___x_2048_ = l_Lean_Meta_mkForallFVars(v_xs_1995_, v_type_1996_, v___x_2046_, v___x_2009_, v___x_2009_, v___x_2047_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
lean_dec_ref(v_xs_1995_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2074_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2051_ = v___x_2048_;
v_isShared_2052_ = v_isSharedCheck_2074_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2048_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2074_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
lean_inc(v_a_2049_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set_tag(v___x_2051_, 1);
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_Meta_mkForallFVars_x27___lam__0(v___x_2017_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v___x_2054_);
lean_dec_ref(v___x_2054_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2063_; 
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; 
v_unused_2064_ = lean_ctor_get(v___x_2055_, 0);
lean_dec(v_unused_2064_);
v___x_2057_ = v___x_2055_;
v_isShared_2058_ = v_isSharedCheck_2063_;
goto v_resetjp_2056_;
}
else
{
lean_dec(v___x_2055_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2063_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; lean_object* v___x_2061_; 
v___x_2059_ = lean_st_ref_get(v___x_2017_);
lean_dec(v___x_2017_);
lean_dec(v___x_2059_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v_a_2049_);
v___x_2061_ = v___x_2057_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2049_);
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
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec(v_a_2049_);
lean_dec(v___x_2017_);
v_a_2065_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2055_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2055_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
}
else
{
lean_object* v_a_2075_; 
v_a_2075_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_a_2075_);
lean_dec_ref_known(v___x_2048_, 1);
v_a_2019_ = v_a_2075_;
goto v___jp_2018_;
}
}
else
{
lean_object* v_a_2076_; 
lean_dec_ref(v_type_1996_);
lean_dec_ref(v_xs_1995_);
v_a_2076_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2041_, 1);
v_a_2019_ = v_a_2076_;
goto v___jp_2018_;
}
}
else
{
lean_object* v_a_2077_; 
lean_dec_ref(v_type_1996_);
lean_dec_ref(v_xs_1995_);
v_a_2077_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2077_);
lean_dec_ref_known(v___x_2040_, 1);
v_a_2019_ = v_a_2077_;
goto v___jp_2018_;
}
v___jp_2018_:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_box(0);
v___x_2021_ = l_Lean_Meta_mkForallFVars_x27___lam__0(v___x_2017_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v___x_2020_);
lean_dec(v___x_2017_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2028_ == 0)
{
lean_object* v_unused_2029_; 
v_unused_2029_ = lean_ctor_get(v___x_2021_, 0);
lean_dec(v_unused_2029_);
v___x_2023_ = v___x_2021_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_dec(v___x_2021_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
lean_ctor_set_tag(v___x_2023_, 1);
lean_ctor_set(v___x_2023_, 0, v_a_2019_);
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2019_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec_ref(v_a_2019_);
v_a_2030_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2021_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2021_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec_ref(v_type_1996_);
lean_dec_ref(v_xs_1995_);
v_a_2078_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2012_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2012_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
v___jp_2002_:
{
uint8_t v___x_2004_; uint8_t v___x_2005_; lean_object* v___x_2006_; 
v___x_2004_ = 1;
v___x_2005_ = 1;
v___x_2006_ = l_Lean_Meta_mkForallFVars(v_xs_1995_, v_type_1996_, v_a_2003_, v___x_2004_, v___x_2004_, v___x_2005_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
lean_dec_ref(v_xs_1995_);
return v___x_2006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___boxed(lean_object* v_xs_2086_, lean_object* v_type_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Lean_Meta_mkForallFVars_x27(v_xs_2086_, v_type_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_);
lean_dec(v_a_2091_);
lean_dec_ref(v_a_2090_);
lean_dec(v_a_2089_);
lean_dec_ref(v_a_2088_);
return v_res_2093_;
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
