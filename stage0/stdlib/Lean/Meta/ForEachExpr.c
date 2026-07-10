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
uint8_t lean_bool_not(uint8_t);
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
lean_object* v___x_271_; lean_object* v___f_272_; lean_object* v___f_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_887__overap_276_; lean_object* v___x_277_; 
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
v___x_887__overap_276_ = l_Lean_Meta_visitForall___redArg(v___x_264_, v___x_274_, v___x_275_, v_e_256_);
lean_inc(v_a_265_);
v___x_277_ = lean_apply_1(v___x_887__overap_276_, v_a_265_);
return v___x_277_;
}
case 6:
{
lean_object* v___x_278_; lean_object* v___f_279_; lean_object* v___f_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_897__overap_283_; lean_object* v___x_284_; 
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
v___x_897__overap_283_ = l_Lean_Meta_visitLambda___redArg(v___x_264_, v___x_281_, v___x_282_, v_e_256_);
lean_inc(v_a_265_);
v___x_284_ = lean_apply_1(v___x_897__overap_283_, v_a_265_);
return v___x_284_;
}
case 8:
{
lean_object* v___x_285_; lean_object* v___f_286_; lean_object* v___f_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_908__overap_290_; lean_object* v___x_291_; 
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
v___x_908__overap_290_ = l_Lean_Meta_visitLet___redArg(v___x_264_, v___x_288_, v___x_289_, v_e_256_);
lean_inc(v_a_265_);
v___x_291_ = lean_apply_1(v___x_908__overap_290_, v_a_265_);
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
lean_dec_ref_known(v_e_256_, 2);
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
lean_dec_ref_known(v_e_256_, 2);
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
lean_dec_ref_known(v_e_256_, 3);
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
lean_dec_ref_known(v_x_487_, 1);
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
uint8_t v___x_593_; uint8_t v___x_594_; 
v___x_593_ = l_Lean_Expr_hasMVar(v_e_590_);
v___x_594_ = lean_bool_not(v___x_593_);
if (v___x_594_ == 0)
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
else
{
lean_object* v___x_615_; 
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v_e_590_);
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg___boxed(lean_object* v_e_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(v_e_616_, v___y_617_);
lean_dec(v___y_617_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3(lean_object* v_e_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(v_e_620_, v___y_622_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___boxed(lean_object* v_e_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3(v_e_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0(lean_object* v_a_634_, lean_object* v___x_635_, lean_object* v_val_636_, lean_object* v___x_637_, lean_object* v_xs_638_, lean_object* v_x_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = lean_array_get_size(v_xs_638_);
v___x_646_ = lean_nat_dec_lt(v_a_634_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
lean_dec(v___x_637_);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_635_);
return v___x_647_;
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = l_Lean_instInhabitedExpr;
v___x_649_ = lean_array_get_borrowed(v___x_648_, v_xs_638_, v_a_634_);
v___x_650_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_649_, v___y_640_, v___y_642_, v___y_643_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
v___x_652_ = l_Lean_LocalDecl_userName(v_a_651_);
lean_dec(v_a_651_);
v___x_653_ = l_Lean_Core_mkFreshUserName(v___x_652_, v___y_642_, v___y_643_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_679_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_679_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_679_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_679_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v_mctx_662_; lean_object* v_cache_663_; lean_object* v_zetaDeltaFVarIds_664_; lean_object* v_postponed_665_; lean_object* v_diag_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_678_; 
v___x_658_ = lean_st_ref_take(v_val_636_);
lean_inc(v___x_637_);
v___x_659_ = lean_array_push(v___x_658_, v___x_637_);
v___x_660_ = lean_st_ref_set(v_val_636_, v___x_659_);
v___x_661_ = lean_st_ref_take(v___y_641_);
v_mctx_662_ = lean_ctor_get(v___x_661_, 0);
v_cache_663_ = lean_ctor_get(v___x_661_, 1);
v_zetaDeltaFVarIds_664_ = lean_ctor_get(v___x_661_, 2);
v_postponed_665_ = lean_ctor_get(v___x_661_, 3);
v_diag_666_ = lean_ctor_get(v___x_661_, 4);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_678_ == 0)
{
v___x_668_ = v___x_661_;
v_isShared_669_ = v_isSharedCheck_678_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_diag_666_);
lean_inc(v_postponed_665_);
lean_inc(v_zetaDeltaFVarIds_664_);
lean_inc(v_cache_663_);
lean_inc(v_mctx_662_);
lean_dec(v___x_661_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_678_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_670_ = l_Lean_MetavarContext_setMVarUserNameTemporarily(v_mctx_662_, v___x_637_, v_a_654_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_670_);
v___x_672_ = v___x_668_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_cache_663_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v_zetaDeltaFVarIds_664_);
lean_ctor_set(v_reuseFailAlloc_677_, 3, v_postponed_665_);
lean_ctor_set(v_reuseFailAlloc_677_, 4, v_diag_666_);
v___x_672_ = v_reuseFailAlloc_677_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = lean_st_ref_set(v___y_641_, v___x_672_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_635_);
v___x_675_ = v___x_656_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_635_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec(v___x_637_);
v_a_680_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_653_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_653_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_dec(v___x_637_);
v_a_688_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_650_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_650_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0___boxed(lean_object* v_a_696_, lean_object* v___x_697_, lean_object* v_val_698_, lean_object* v___x_699_, lean_object* v_xs_700_, lean_object* v_x_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0(v_a_696_, v___x_697_, v_val_698_, v___x_699_, v_xs_700_, v_x_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec_ref(v_x_701_);
lean_dec_ref(v_xs_700_);
lean_dec(v_val_698_);
lean_dec(v_a_696_);
return v_res_707_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(lean_object* v_a_708_, lean_object* v_as_709_, size_t v_i_710_, size_t v_stop_711_){
_start:
{
uint8_t v___x_712_; 
v___x_712_ = lean_usize_dec_eq(v_i_710_, v_stop_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_713_ = lean_array_uget_borrowed(v_as_709_, v_i_710_);
v___x_714_ = lean_expr_eqv(v_a_708_, v___x_713_);
if (v___x_714_ == 0)
{
size_t v___x_715_; size_t v___x_716_; 
v___x_715_ = ((size_t)1ULL);
v___x_716_ = lean_usize_add(v_i_710_, v___x_715_);
v_i_710_ = v___x_716_;
goto _start;
}
else
{
return v___x_714_;
}
}
else
{
uint8_t v___x_718_; 
v___x_718_ = 0;
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1___boxed(lean_object* v_a_719_, lean_object* v_as_720_, lean_object* v_i_721_, lean_object* v_stop_722_){
_start:
{
size_t v_i_boxed_723_; size_t v_stop_boxed_724_; uint8_t v_res_725_; lean_object* v_r_726_; 
v_i_boxed_723_ = lean_unbox_usize(v_i_721_);
lean_dec(v_i_721_);
v_stop_boxed_724_ = lean_unbox_usize(v_stop_722_);
lean_dec(v_stop_722_);
v_res_725_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(v_a_719_, v_as_720_, v_i_boxed_723_, v_stop_boxed_724_);
lean_dec_ref(v_as_720_);
lean_dec_ref(v_a_719_);
v_r_726_ = lean_box(v_res_725_);
return v_r_726_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(lean_object* v_as_727_, lean_object* v_a_728_){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_729_ = lean_unsigned_to_nat(0u);
v___x_730_ = lean_array_get_size(v_as_727_);
v___x_731_ = lean_nat_dec_lt(v___x_729_, v___x_730_);
if (v___x_731_ == 0)
{
return v___x_731_;
}
else
{
if (v___x_731_ == 0)
{
return v___x_731_;
}
else
{
size_t v___x_732_; size_t v___x_733_; uint8_t v___x_734_; 
v___x_732_ = ((size_t)0ULL);
v___x_733_ = lean_usize_of_nat(v___x_730_);
v___x_734_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(v_a_728_, v_as_727_, v___x_732_, v___x_733_);
return v___x_734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1___boxed(lean_object* v_as_735_, lean_object* v_a_736_){
_start:
{
uint8_t v_res_737_; lean_object* v_r_738_; 
v_res_737_ = l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(v_as_735_, v_a_736_);
lean_dec_ref(v_a_736_);
lean_dec_ref(v_as_735_);
v_r_738_ = lean_box(v_res_737_);
return v_r_738_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(lean_object* v_upperBound_739_, lean_object* v___x_740_, lean_object* v_val_741_, lean_object* v_e_742_, lean_object* v_isTarget_743_, lean_object* v_a_744_, lean_object* v_b_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_a_752_; uint8_t v___x_756_; 
v___x_756_ = lean_nat_dec_lt(v_a_744_, v_upperBound_739_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; 
lean_dec(v_a_744_);
lean_dec(v_val_741_);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v_b_745_);
return v___x_757_;
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___y_761_; uint8_t v___x_792_; 
v___x_758_ = lean_box(0);
v___x_759_ = lean_array_fget_borrowed(v___x_740_, v_a_744_);
v___x_792_ = l_Lean_Expr_isMVar(v___x_759_);
if (v___x_792_ == 0)
{
v___y_761_ = v___x_792_;
goto v___jp_760_;
}
else
{
uint8_t v___x_793_; 
v___x_793_ = l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(v_isTarget_743_, v___x_759_);
v___y_761_ = v___x_793_;
goto v___jp_760_;
}
v___jp_760_:
{
if (v___y_761_ == 0)
{
v_a_752_ = v___x_758_;
goto v___jp_751_;
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = l_Lean_Expr_mvarId_x21(v___x_759_);
lean_inc(v___x_762_);
v___x_763_ = l_Lean_MVarId_getDecl(v___x_762_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v_userName_765_; uint8_t v___x_766_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v_userName_765_ = lean_ctor_get(v_a_764_, 0);
lean_inc(v_userName_765_);
lean_dec(v_a_764_);
v___x_766_ = l_Lean_Name_isAnonymous(v_userName_765_);
lean_dec(v_userName_765_);
if (v___x_766_ == 0)
{
lean_dec(v___x_762_);
v_a_752_ = v___x_758_;
goto v___jp_751_;
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = l_Lean_Expr_getAppFn(v_e_742_);
lean_inc(v___y_749_);
lean_inc_ref(v___y_748_);
lean_inc(v___y_747_);
lean_inc_ref(v___y_746_);
v___x_768_ = lean_infer_type(v___x_767_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; lean_object* v___x_775_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
lean_inc(v_val_741_);
lean_inc(v_a_744_);
v___f_770_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_770_, 0, v_a_744_);
lean_closure_set(v___f_770_, 1, v___x_758_);
lean_closure_set(v___f_770_, 2, v_val_741_);
lean_closure_set(v___f_770_, 3, v___x_762_);
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = lean_nat_add(v_a_744_, v___x_771_);
v___x_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
v___x_774_ = 0;
v___x_775_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(v_a_769_, v___x_773_, v___f_770_, v___x_774_, v___x_774_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_dec_ref_known(v___x_775_, 1);
v_a_752_ = v___x_758_;
goto v___jp_751_;
}
else
{
lean_dec(v_a_744_);
lean_dec(v_val_741_);
return v___x_775_;
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec(v___x_762_);
lean_dec(v_a_744_);
lean_dec(v_val_741_);
v_a_776_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_768_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_768_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec(v___x_762_);
lean_dec(v_a_744_);
lean_dec(v_val_741_);
v_a_784_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_763_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_763_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
}
v___jp_751_:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_unsigned_to_nat(1u);
v___x_754_ = lean_nat_add(v_a_744_, v___x_753_);
lean_dec(v_a_744_);
v_a_744_ = v___x_754_;
v_b_745_ = v_a_752_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___boxed(lean_object* v_upperBound_794_, lean_object* v___x_795_, lean_object* v_val_796_, lean_object* v_e_797_, lean_object* v_isTarget_798_, lean_object* v_a_799_, lean_object* v_b_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(v_upperBound_794_, v___x_795_, v_val_796_, v_e_797_, v_isTarget_798_, v_a_799_, v_b_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec_ref(v_isTarget_798_);
lean_dec_ref(v_e_797_);
lean_dec_ref(v___x_795_);
lean_dec(v_upperBound_794_);
return v_res_806_;
}
}
static lean_object* _init_l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0(void){
_start:
{
lean_object* v___x_807_; lean_object* v_dummy_808_; 
v___x_807_ = lean_box(0);
v_dummy_808_ = l_Lean_Expr_sort___override(v___x_807_);
return v_dummy_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___lam__0(lean_object* v_val_809_, lean_object* v_isTarget_810_, lean_object* v___x_811_, lean_object* v_e_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
uint8_t v___x_818_; 
v___x_818_ = l_Lean_Expr_isApp(v_e_812_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; 
lean_dec_ref(v_e_812_);
lean_dec(v___x_811_);
lean_dec(v_val_809_);
v___x_819_ = lean_box(0);
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
return v___x_820_;
}
else
{
lean_object* v_dummy_821_; lean_object* v_nargs_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_dummy_821_ = lean_obj_once(&l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0, &l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0_once, _init_l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0);
v_nargs_822_ = l_Lean_Expr_getAppNumArgs(v_e_812_);
lean_inc(v_nargs_822_);
v___x_823_ = lean_mk_array(v_nargs_822_, v_dummy_821_);
v___x_824_ = lean_unsigned_to_nat(1u);
v___x_825_ = lean_nat_sub(v_nargs_822_, v___x_824_);
lean_dec(v_nargs_822_);
lean_inc_ref(v_e_812_);
v___x_826_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_812_, v___x_823_, v___x_825_);
v___x_827_ = lean_array_get_size(v___x_826_);
v___x_828_ = lean_box(0);
v___x_829_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(v___x_827_, v___x_826_, v_val_809_, v_e_812_, v_isTarget_810_, v___x_811_, v___x_828_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec_ref(v_e_812_);
lean_dec_ref(v___x_826_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; 
v_unused_837_ = lean_ctor_get(v___x_829_, 0);
lean_dec(v_unused_837_);
v___x_831_ = v___x_829_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_dec(v___x_829_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_828_);
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_828_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
else
{
return v___x_829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___lam__0___boxed(lean_object* v_val_838_, lean_object* v_isTarget_839_, lean_object* v___x_840_, lean_object* v_e_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_Meta_setMVarUserNamesAt___lam__0(v_val_838_, v_isTarget_839_, v___x_840_, v_e_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec_ref(v_isTarget_839_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0(lean_object* v_k_848_, lean_object* v___y_849_, lean_object* v_b_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___x_856_; 
lean_inc(v___y_854_);
lean_inc_ref(v___y_853_);
lean_inc(v___y_852_);
lean_inc_ref(v___y_851_);
lean_inc(v___y_849_);
v___x_856_ = lean_apply_7(v_k_848_, v_b_850_, v___y_849_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, lean_box(0));
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0___boxed(lean_object* v_k_857_, lean_object* v___y_858_, lean_object* v_b_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0(v_k_857_, v___y_858_, v_b_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_858_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(lean_object* v_name_866_, uint8_t v_bi_867_, lean_object* v_type_868_, lean_object* v_k_869_, uint8_t v_kind_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v___f_877_; lean_object* v___x_878_; 
lean_inc(v___y_871_);
v___f_877_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_877_, 0, v_k_869_);
lean_closure_set(v___f_877_, 1, v___y_871_);
v___x_878_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_866_, v_bi_867_, v_type_868_, v___f_877_, v_kind_870_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
if (lean_obj_tag(v___x_878_) == 0)
{
return v___x_878_;
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___boxed(lean_object* v_name_887_, lean_object* v_bi_888_, lean_object* v_type_889_, lean_object* v_k_890_, lean_object* v_kind_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
uint8_t v_bi_boxed_898_; uint8_t v_kind_boxed_899_; lean_object* v_res_900_; 
v_bi_boxed_898_ = lean_unbox(v_bi_888_);
v_kind_boxed_899_ = lean_unbox(v_kind_891_);
v_res_900_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_name_887_, v_bi_boxed_898_, v_type_889_, v_k_890_, v_kind_boxed_899_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0___boxed(lean_object* v_fvars_901_, lean_object* v_f_902_, lean_object* v_body_903_, lean_object* v_x_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0(v_fvars_901_, v_f_902_, v_body_903_, v_x_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(lean_object* v_f_912_, lean_object* v_fvars_913_, lean_object* v_a_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
if (lean_obj_tag(v_a_914_) == 6)
{
lean_object* v_binderName_921_; lean_object* v_binderType_922_; lean_object* v_body_923_; uint8_t v_binderInfo_924_; lean_object* v_d_925_; lean_object* v___x_926_; 
v_binderName_921_ = lean_ctor_get(v_a_914_, 0);
lean_inc(v_binderName_921_);
v_binderType_922_ = lean_ctor_get(v_a_914_, 1);
lean_inc_ref(v_binderType_922_);
v_body_923_ = lean_ctor_get(v_a_914_, 2);
lean_inc_ref(v_body_923_);
v_binderInfo_924_ = lean_ctor_get_uint8(v_a_914_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_914_, 3);
v_d_925_ = lean_expr_instantiate_rev(v_binderType_922_, v_fvars_913_);
lean_dec_ref(v_binderType_922_);
lean_inc_ref(v_f_912_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
lean_inc(v___y_915_);
lean_inc_ref(v_d_925_);
v___x_926_ = lean_apply_7(v_f_912_, v_d_925_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, lean_box(0));
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v___f_927_; uint8_t v___x_928_; lean_object* v___x_929_; 
lean_dec_ref_known(v___x_926_, 1);
v___f_927_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0___boxed), 10, 3);
lean_closure_set(v___f_927_, 0, v_fvars_913_);
lean_closure_set(v___f_927_, 1, v_f_912_);
lean_closure_set(v___f_927_, 2, v_body_923_);
v___x_928_ = 0;
v___x_929_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_binderName_921_, v_binderInfo_924_, v_d_925_, v___f_927_, v___x_928_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
return v___x_929_;
}
else
{
lean_dec_ref(v_d_925_);
lean_dec_ref(v_body_923_);
lean_dec(v_binderName_921_);
lean_dec_ref(v_fvars_913_);
lean_dec_ref(v_f_912_);
return v___x_926_;
}
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_expr_instantiate_rev(v_a_914_, v_fvars_913_);
lean_dec_ref(v_fvars_913_);
lean_dec_ref(v_a_914_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
lean_inc(v___y_915_);
v___x_931_ = lean_apply_7(v_f_912_, v___x_930_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, lean_box(0));
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0(lean_object* v_fvars_932_, lean_object* v_f_933_, lean_object* v_body_934_, lean_object* v_x_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_array_push(v_fvars_932_, v_x_935_);
v___x_943_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(v_f_933_, v___x_942_, v_body_934_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___boxed(lean_object* v_f_944_, lean_object* v_fvars_945_, lean_object* v_a_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(v_f_944_, v_fvars_945_, v_a_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(lean_object* v_f_954_, lean_object* v_e_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_963_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(v_f_954_, v___x_962_, v_e_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10___boxed(lean_object* v_f_964_, lean_object* v_e_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(v_f_964_, v_e_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_object* v_00_u03b1_973_, lean_object* v_x_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_apply_1(v_x_974_, lean_box(0));
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0___boxed(lean_object* v_00_u03b1_982_, lean_object* v_x_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(v_00_u03b1_982_, v_x_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0___boxed(lean_object* v_fvars_990_, lean_object* v_f_991_, lean_object* v_body_992_, lean_object* v_x_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0(v_fvars_990_, v_f_991_, v_body_992_, v_x_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(lean_object* v_f_1001_, lean_object* v_fvars_1002_, lean_object* v_a_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
if (lean_obj_tag(v_a_1003_) == 7)
{
lean_object* v_binderName_1010_; lean_object* v_binderType_1011_; lean_object* v_body_1012_; uint8_t v_binderInfo_1013_; lean_object* v_d_1014_; lean_object* v___x_1015_; 
v_binderName_1010_ = lean_ctor_get(v_a_1003_, 0);
lean_inc(v_binderName_1010_);
v_binderType_1011_ = lean_ctor_get(v_a_1003_, 1);
lean_inc_ref(v_binderType_1011_);
v_body_1012_ = lean_ctor_get(v_a_1003_, 2);
lean_inc_ref(v_body_1012_);
v_binderInfo_1013_ = lean_ctor_get_uint8(v_a_1003_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_1003_, 3);
v_d_1014_ = lean_expr_instantiate_rev(v_binderType_1011_, v_fvars_1002_);
lean_dec_ref(v_binderType_1011_);
lean_inc_ref(v_f_1001_);
lean_inc(v___y_1008_);
lean_inc_ref(v___y_1007_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
lean_inc_ref(v_d_1014_);
v___x_1015_ = lean_apply_7(v_f_1001_, v_d_1014_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, lean_box(0));
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v___f_1016_; uint8_t v___x_1017_; lean_object* v___x_1018_; 
lean_dec_ref_known(v___x_1015_, 1);
v___f_1016_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1016_, 0, v_fvars_1002_);
lean_closure_set(v___f_1016_, 1, v_f_1001_);
lean_closure_set(v___f_1016_, 2, v_body_1012_);
v___x_1017_ = 0;
v___x_1018_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_binderName_1010_, v_binderInfo_1013_, v_d_1014_, v___f_1016_, v___x_1017_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
return v___x_1018_;
}
else
{
lean_dec_ref(v_d_1014_);
lean_dec_ref(v_body_1012_);
lean_dec(v_binderName_1010_);
lean_dec_ref(v_fvars_1002_);
lean_dec_ref(v_f_1001_);
return v___x_1015_;
}
}
else
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_expr_instantiate_rev(v_a_1003_, v_fvars_1002_);
lean_dec_ref(v_fvars_1002_);
lean_dec_ref(v_a_1003_);
lean_inc(v___y_1008_);
lean_inc_ref(v___y_1007_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
v___x_1020_ = lean_apply_7(v_f_1001_, v___x_1019_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, lean_box(0));
return v___x_1020_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0(lean_object* v_fvars_1021_, lean_object* v_f_1022_, lean_object* v_body_1023_, lean_object* v_x_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_array_push(v_fvars_1021_, v_x_1024_);
v___x_1032_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(v_f_1022_, v___x_1031_, v_body_1023_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___boxed(lean_object* v_f_1033_, lean_object* v_fvars_1034_, lean_object* v_a_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(v_f_1033_, v_fvars_1034_, v_a_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(lean_object* v_f_1043_, lean_object* v_e_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_1052_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(v_f_1043_, v___x_1051_, v_e_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9___boxed(lean_object* v_f_1053_, lean_object* v_e_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(v_f_1053_, v_e_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_a_1062_, lean_object* v_x_1063_){
_start:
{
if (lean_obj_tag(v_x_1063_) == 0)
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_box(0);
return v___x_1064_;
}
else
{
lean_object* v_key_1065_; lean_object* v_value_1066_; lean_object* v_tail_1067_; uint8_t v___x_1068_; 
v_key_1065_ = lean_ctor_get(v_x_1063_, 0);
v_value_1066_ = lean_ctor_get(v_x_1063_, 1);
v_tail_1067_ = lean_ctor_get(v_x_1063_, 2);
v___x_1068_ = lean_expr_eqv(v_key_1065_, v_a_1062_);
if (v___x_1068_ == 0)
{
v_x_1063_ = v_tail_1067_;
goto _start;
}
else
{
lean_object* v___x_1070_; 
lean_inc(v_value_1066_);
v___x_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1070_, 0, v_value_1066_);
return v___x_1070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_a_1071_, lean_object* v_x_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(v_a_1071_, v_x_1072_);
lean_dec(v_x_1072_);
lean_dec_ref(v_a_1071_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_m_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_buckets_1076_; lean_object* v___x_1077_; uint64_t v___x_1078_; uint64_t v___x_1079_; uint64_t v___x_1080_; uint64_t v_fold_1081_; uint64_t v___x_1082_; uint64_t v___x_1083_; uint64_t v___x_1084_; size_t v___x_1085_; size_t v___x_1086_; size_t v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_buckets_1076_ = lean_ctor_get(v_m_1074_, 1);
v___x_1077_ = lean_array_get_size(v_buckets_1076_);
v___x_1078_ = l_Lean_Expr_hash(v_a_1075_);
v___x_1079_ = 32ULL;
v___x_1080_ = lean_uint64_shift_right(v___x_1078_, v___x_1079_);
v_fold_1081_ = lean_uint64_xor(v___x_1078_, v___x_1080_);
v___x_1082_ = 16ULL;
v___x_1083_ = lean_uint64_shift_right(v_fold_1081_, v___x_1082_);
v___x_1084_ = lean_uint64_xor(v_fold_1081_, v___x_1083_);
v___x_1085_ = lean_uint64_to_usize(v___x_1084_);
v___x_1086_ = lean_usize_of_nat(v___x_1077_);
v___x_1087_ = ((size_t)1ULL);
v___x_1088_ = lean_usize_sub(v___x_1086_, v___x_1087_);
v___x_1089_ = lean_usize_land(v___x_1085_, v___x_1088_);
v___x_1090_ = lean_array_uget_borrowed(v_buckets_1076_, v___x_1089_);
v___x_1091_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(v_a_1075_, v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_m_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_m_1092_, v_a_1093_);
lean_dec_ref(v_a_1093_);
lean_dec_ref(v_m_1092_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(lean_object* v_a_1095_, lean_object* v_b_1096_, lean_object* v_x_1097_){
_start:
{
if (lean_obj_tag(v_x_1097_) == 0)
{
lean_dec(v_b_1096_);
lean_dec_ref(v_a_1095_);
return v_x_1097_;
}
else
{
lean_object* v_key_1098_; lean_object* v_value_1099_; lean_object* v_tail_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1112_; 
v_key_1098_ = lean_ctor_get(v_x_1097_, 0);
v_value_1099_ = lean_ctor_get(v_x_1097_, 1);
v_tail_1100_ = lean_ctor_get(v_x_1097_, 2);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_x_1097_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1102_ = v_x_1097_;
v_isShared_1103_ = v_isSharedCheck_1112_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_tail_1100_);
lean_inc(v_value_1099_);
lean_inc(v_key_1098_);
lean_dec(v_x_1097_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1112_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
uint8_t v___x_1104_; 
v___x_1104_ = lean_expr_eqv(v_key_1098_, v_a_1095_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1105_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(v_a_1095_, v_b_1096_, v_tail_1100_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 2, v___x_1105_);
v___x_1107_ = v___x_1102_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_key_1098_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_value_1099_);
lean_ctor_set(v_reuseFailAlloc_1108_, 2, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
else
{
lean_object* v___x_1110_; 
lean_dec(v_value_1099_);
lean_dec(v_key_1098_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 1, v_b_1096_);
lean_ctor_set(v___x_1102_, 0, v_a_1095_);
v___x_1110_ = v___x_1102_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1095_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_b_1096_);
lean_ctor_set(v_reuseFailAlloc_1111_, 2, v_tail_1100_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16___redArg(lean_object* v_x_1113_, lean_object* v_x_1114_){
_start:
{
if (lean_obj_tag(v_x_1114_) == 0)
{
return v_x_1113_;
}
else
{
lean_object* v_key_1115_; lean_object* v_value_1116_; lean_object* v_tail_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1140_; 
v_key_1115_ = lean_ctor_get(v_x_1114_, 0);
v_value_1116_ = lean_ctor_get(v_x_1114_, 1);
v_tail_1117_ = lean_ctor_get(v_x_1114_, 2);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_x_1114_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1119_ = v_x_1114_;
v_isShared_1120_ = v_isSharedCheck_1140_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_tail_1117_);
lean_inc(v_value_1116_);
lean_inc(v_key_1115_);
lean_dec(v_x_1114_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1140_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; uint64_t v___x_1122_; uint64_t v___x_1123_; uint64_t v___x_1124_; uint64_t v_fold_1125_; uint64_t v___x_1126_; uint64_t v___x_1127_; uint64_t v___x_1128_; size_t v___x_1129_; size_t v___x_1130_; size_t v___x_1131_; size_t v___x_1132_; size_t v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1121_ = lean_array_get_size(v_x_1113_);
v___x_1122_ = l_Lean_Expr_hash(v_key_1115_);
v___x_1123_ = 32ULL;
v___x_1124_ = lean_uint64_shift_right(v___x_1122_, v___x_1123_);
v_fold_1125_ = lean_uint64_xor(v___x_1122_, v___x_1124_);
v___x_1126_ = 16ULL;
v___x_1127_ = lean_uint64_shift_right(v_fold_1125_, v___x_1126_);
v___x_1128_ = lean_uint64_xor(v_fold_1125_, v___x_1127_);
v___x_1129_ = lean_uint64_to_usize(v___x_1128_);
v___x_1130_ = lean_usize_of_nat(v___x_1121_);
v___x_1131_ = ((size_t)1ULL);
v___x_1132_ = lean_usize_sub(v___x_1130_, v___x_1131_);
v___x_1133_ = lean_usize_land(v___x_1129_, v___x_1132_);
v___x_1134_ = lean_array_uget_borrowed(v_x_1113_, v___x_1133_);
lean_inc(v___x_1134_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 2, v___x_1134_);
v___x_1136_ = v___x_1119_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_key_1115_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v_value_1116_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_array_uset(v_x_1113_, v___x_1133_, v___x_1136_);
v_x_1113_ = v___x_1137_;
v_x_1114_ = v_tail_1117_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12___redArg(lean_object* v_i_1141_, lean_object* v_source_1142_, lean_object* v_target_1143_){
_start:
{
lean_object* v___x_1144_; uint8_t v___x_1145_; 
v___x_1144_ = lean_array_get_size(v_source_1142_);
v___x_1145_ = lean_nat_dec_lt(v_i_1141_, v___x_1144_);
if (v___x_1145_ == 0)
{
lean_dec_ref(v_source_1142_);
lean_dec(v_i_1141_);
return v_target_1143_;
}
else
{
lean_object* v_es_1146_; lean_object* v___x_1147_; lean_object* v_source_1148_; lean_object* v_target_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v_es_1146_ = lean_array_fget(v_source_1142_, v_i_1141_);
v___x_1147_ = lean_box(0);
v_source_1148_ = lean_array_fset(v_source_1142_, v_i_1141_, v___x_1147_);
v_target_1149_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16___redArg(v_target_1143_, v_es_1146_);
v___x_1150_ = lean_unsigned_to_nat(1u);
v___x_1151_ = lean_nat_add(v_i_1141_, v___x_1150_);
lean_dec(v_i_1141_);
v_i_1141_ = v___x_1151_;
v_source_1142_ = v_source_1148_;
v_target_1143_ = v_target_1149_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11___redArg(lean_object* v_data_1153_){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v_nbuckets_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1154_ = lean_array_get_size(v_data_1153_);
v___x_1155_ = lean_unsigned_to_nat(2u);
v_nbuckets_1156_ = lean_nat_mul(v___x_1154_, v___x_1155_);
v___x_1157_ = lean_unsigned_to_nat(0u);
v___x_1158_ = lean_box(0);
v___x_1159_ = lean_mk_array(v_nbuckets_1156_, v___x_1158_);
v___x_1160_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12___redArg(v___x_1157_, v_data_1153_, v___x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(lean_object* v_a_1161_, lean_object* v_x_1162_){
_start:
{
if (lean_obj_tag(v_x_1162_) == 0)
{
uint8_t v___x_1163_; 
v___x_1163_ = 0;
return v___x_1163_;
}
else
{
lean_object* v_key_1164_; lean_object* v_tail_1165_; uint8_t v___x_1166_; 
v_key_1164_ = lean_ctor_get(v_x_1162_, 0);
v_tail_1165_ = lean_ctor_get(v_x_1162_, 2);
v___x_1166_ = lean_expr_eqv(v_key_1164_, v_a_1161_);
if (v___x_1166_ == 0)
{
v_x_1162_ = v_tail_1165_;
goto _start;
}
else
{
return v___x_1166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_a_1168_, lean_object* v_x_1169_){
_start:
{
uint8_t v_res_1170_; lean_object* v_r_1171_; 
v_res_1170_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_a_1168_, v_x_1169_);
lean_dec(v_x_1169_);
lean_dec_ref(v_a_1168_);
v_r_1171_ = lean_box(v_res_1170_);
return v_r_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(lean_object* v_m_1172_, lean_object* v_a_1173_, lean_object* v_b_1174_){
_start:
{
lean_object* v_size_1175_; lean_object* v_buckets_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1219_; 
v_size_1175_ = lean_ctor_get(v_m_1172_, 0);
v_buckets_1176_ = lean_ctor_get(v_m_1172_, 1);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_m_1172_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1178_ = v_m_1172_;
v_isShared_1179_ = v_isSharedCheck_1219_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_buckets_1176_);
lean_inc(v_size_1175_);
lean_dec(v_m_1172_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1219_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; uint64_t v___x_1181_; uint64_t v___x_1182_; uint64_t v___x_1183_; uint64_t v_fold_1184_; uint64_t v___x_1185_; uint64_t v___x_1186_; uint64_t v___x_1187_; size_t v___x_1188_; size_t v___x_1189_; size_t v___x_1190_; size_t v___x_1191_; size_t v___x_1192_; lean_object* v_bkt_1193_; uint8_t v___x_1194_; 
v___x_1180_ = lean_array_get_size(v_buckets_1176_);
v___x_1181_ = l_Lean_Expr_hash(v_a_1173_);
v___x_1182_ = 32ULL;
v___x_1183_ = lean_uint64_shift_right(v___x_1181_, v___x_1182_);
v_fold_1184_ = lean_uint64_xor(v___x_1181_, v___x_1183_);
v___x_1185_ = 16ULL;
v___x_1186_ = lean_uint64_shift_right(v_fold_1184_, v___x_1185_);
v___x_1187_ = lean_uint64_xor(v_fold_1184_, v___x_1186_);
v___x_1188_ = lean_uint64_to_usize(v___x_1187_);
v___x_1189_ = lean_usize_of_nat(v___x_1180_);
v___x_1190_ = ((size_t)1ULL);
v___x_1191_ = lean_usize_sub(v___x_1189_, v___x_1190_);
v___x_1192_ = lean_usize_land(v___x_1188_, v___x_1191_);
v_bkt_1193_ = lean_array_uget_borrowed(v_buckets_1176_, v___x_1192_);
v___x_1194_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_a_1173_, v_bkt_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v_size_x27_1196_; lean_object* v___x_1197_; lean_object* v_buckets_x27_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1195_ = lean_unsigned_to_nat(1u);
v_size_x27_1196_ = lean_nat_add(v_size_1175_, v___x_1195_);
lean_dec(v_size_1175_);
lean_inc(v_bkt_1193_);
v___x_1197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1197_, 0, v_a_1173_);
lean_ctor_set(v___x_1197_, 1, v_b_1174_);
lean_ctor_set(v___x_1197_, 2, v_bkt_1193_);
v_buckets_x27_1198_ = lean_array_uset(v_buckets_1176_, v___x_1192_, v___x_1197_);
v___x_1199_ = lean_unsigned_to_nat(4u);
v___x_1200_ = lean_nat_mul(v_size_x27_1196_, v___x_1199_);
v___x_1201_ = lean_unsigned_to_nat(3u);
v___x_1202_ = lean_nat_div(v___x_1200_, v___x_1201_);
lean_dec(v___x_1200_);
v___x_1203_ = lean_array_get_size(v_buckets_x27_1198_);
v___x_1204_ = lean_nat_dec_le(v___x_1202_, v___x_1203_);
lean_dec(v___x_1202_);
if (v___x_1204_ == 0)
{
lean_object* v_val_1205_; lean_object* v___x_1207_; 
v_val_1205_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11___redArg(v_buckets_x27_1198_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v_val_1205_);
lean_ctor_set(v___x_1178_, 0, v_size_x27_1196_);
v___x_1207_ = v___x_1178_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_size_x27_1196_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_val_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
else
{
lean_object* v___x_1210_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v_buckets_x27_1198_);
lean_ctor_set(v___x_1178_, 0, v_size_x27_1196_);
v___x_1210_ = v___x_1178_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_size_x27_1196_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_buckets_x27_1198_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
else
{
lean_object* v___x_1212_; lean_object* v_buckets_x27_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
lean_inc(v_bkt_1193_);
v___x_1212_ = lean_box(0);
v_buckets_x27_1213_ = lean_array_uset(v_buckets_1176_, v___x_1192_, v___x_1212_);
v___x_1214_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(v_a_1173_, v_b_1174_, v_bkt_1193_);
v___x_1215_ = lean_array_uset(v_buckets_x27_1213_, v___x_1192_, v___x_1214_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1215_);
v___x_1217_ = v___x_1178_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_size_1175_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1(lean_object* v_a_1220_, lean_object* v_e_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1224_ = lean_st_ref_take(v_a_1220_);
v___x_1225_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(v___x_1224_, v_e_1221_, v_a_1222_);
v___x_1226_ = lean_st_ref_set(v_a_1220_, v___x_1225_);
v___x_1227_ = lean_box(0);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_a_1228_, lean_object* v_e_1229_, lean_object* v_a_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1(v_a_1228_, v_e_1229_, v_a_1230_);
lean_dec(v_a_1228_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(lean_object* v_name_1233_, lean_object* v_type_1234_, lean_object* v_val_1235_, lean_object* v_k_1236_, uint8_t v_nondep_1237_, uint8_t v_kind_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___f_1245_; lean_object* v___x_1246_; 
lean_inc(v___y_1239_);
v___f_1245_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1245_, 0, v_k_1236_);
lean_closure_set(v___f_1245_, 1, v___y_1239_);
v___x_1246_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1233_, v_type_1234_, v_val_1235_, v___f_1245_, v_nondep_1237_, v_kind_1238_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
if (lean_obj_tag(v___x_1246_) == 0)
{
return v___x_1246_;
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg___boxed(lean_object* v_name_1255_, lean_object* v_type_1256_, lean_object* v_val_1257_, lean_object* v_k_1258_, lean_object* v_nondep_1259_, lean_object* v_kind_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
uint8_t v_nondep_boxed_1267_; uint8_t v_kind_boxed_1268_; lean_object* v_res_1269_; 
v_nondep_boxed_1267_ = lean_unbox(v_nondep_1259_);
v_kind_boxed_1268_ = lean_unbox(v_kind_1260_);
v_res_1269_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(v_name_1255_, v_type_1256_, v_val_1257_, v_k_1258_, v_nondep_boxed_1267_, v_kind_boxed_1268_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0___boxed(lean_object* v_fvars_1270_, lean_object* v_f_1271_, lean_object* v_body_1272_, lean_object* v_x_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0(v_fvars_1270_, v_f_1271_, v_body_1272_, v_x_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(lean_object* v_f_1281_, lean_object* v_fvars_1282_, lean_object* v_a_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
if (lean_obj_tag(v_a_1283_) == 8)
{
lean_object* v_declName_1290_; lean_object* v_type_1291_; lean_object* v_value_1292_; lean_object* v_body_1293_; lean_object* v_d_1294_; lean_object* v___x_1295_; 
v_declName_1290_ = lean_ctor_get(v_a_1283_, 0);
lean_inc(v_declName_1290_);
v_type_1291_ = lean_ctor_get(v_a_1283_, 1);
lean_inc_ref(v_type_1291_);
v_value_1292_ = lean_ctor_get(v_a_1283_, 2);
lean_inc_ref(v_value_1292_);
v_body_1293_ = lean_ctor_get(v_a_1283_, 3);
lean_inc_ref(v_body_1293_);
lean_dec_ref_known(v_a_1283_, 4);
v_d_1294_ = lean_expr_instantiate_rev(v_type_1291_, v_fvars_1282_);
lean_dec_ref(v_type_1291_);
lean_inc_ref(v_f_1281_);
lean_inc(v___y_1288_);
lean_inc_ref(v___y_1287_);
lean_inc(v___y_1286_);
lean_inc_ref(v___y_1285_);
lean_inc(v___y_1284_);
lean_inc_ref(v_d_1294_);
v___x_1295_ = lean_apply_7(v_f_1281_, v_d_1294_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, lean_box(0));
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_v_1296_; lean_object* v___x_1297_; 
lean_dec_ref_known(v___x_1295_, 1);
v_v_1296_ = lean_expr_instantiate_rev(v_value_1292_, v_fvars_1282_);
lean_dec_ref(v_value_1292_);
lean_inc_ref(v_f_1281_);
lean_inc(v___y_1288_);
lean_inc_ref(v___y_1287_);
lean_inc(v___y_1286_);
lean_inc_ref(v___y_1285_);
lean_inc(v___y_1284_);
lean_inc_ref(v_v_1296_);
v___x_1297_ = lean_apply_7(v_f_1281_, v_v_1296_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, lean_box(0));
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v___f_1298_; uint8_t v___x_1299_; uint8_t v___x_1300_; lean_object* v___x_1301_; 
lean_dec_ref_known(v___x_1297_, 1);
v___f_1298_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1298_, 0, v_fvars_1282_);
lean_closure_set(v___f_1298_, 1, v_f_1281_);
lean_closure_set(v___f_1298_, 2, v_body_1293_);
v___x_1299_ = 0;
v___x_1300_ = 0;
v___x_1301_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(v_declName_1290_, v_d_1294_, v_v_1296_, v___f_1298_, v___x_1299_, v___x_1300_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
return v___x_1301_;
}
else
{
lean_dec_ref(v_v_1296_);
lean_dec_ref(v_d_1294_);
lean_dec_ref(v_body_1293_);
lean_dec(v_declName_1290_);
lean_dec_ref(v_fvars_1282_);
lean_dec_ref(v_f_1281_);
return v___x_1297_;
}
}
else
{
lean_dec_ref(v_d_1294_);
lean_dec_ref(v_body_1293_);
lean_dec_ref(v_value_1292_);
lean_dec(v_declName_1290_);
lean_dec_ref(v_fvars_1282_);
lean_dec_ref(v_f_1281_);
return v___x_1295_;
}
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = lean_expr_instantiate_rev(v_a_1283_, v_fvars_1282_);
lean_dec_ref(v_fvars_1282_);
lean_dec_ref(v_a_1283_);
lean_inc(v___y_1288_);
lean_inc_ref(v___y_1287_);
lean_inc(v___y_1286_);
lean_inc_ref(v___y_1285_);
lean_inc(v___y_1284_);
v___x_1303_ = lean_apply_7(v_f_1281_, v___x_1302_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, lean_box(0));
return v___x_1303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0(lean_object* v_fvars_1304_, lean_object* v_f_1305_, lean_object* v_body_1306_, lean_object* v_x_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_array_push(v_fvars_1304_, v_x_1307_);
v___x_1315_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(v_f_1305_, v___x_1314_, v_body_1306_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___boxed(lean_object* v_f_1316_, lean_object* v_fvars_1317_, lean_object* v_a_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(v_f_1316_, v_fvars_1317_, v_a_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(lean_object* v_f_1326_, lean_object* v_e_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1334_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_1335_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(v_f_1326_, v___x_1334_, v_e_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11___boxed(lean_object* v_f_1336_, lean_object* v_e_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(v_f_1336_, v_e_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed(lean_object* v_fn_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2(v_fn_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(lean_object* v_fn_1354_, lean_object* v_e_1355_, lean_object* v_a_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_a_1363_; lean_object* v___y_1375_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_inc(v_a_1356_);
v___x_1377_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1377_, 0, lean_box(0));
lean_closure_set(v___x_1377_, 1, lean_box(0));
lean_closure_set(v___x_1377_, 2, v_a_1356_);
v___x_1378_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_box(0), v___x_1377_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1415_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1381_ = v___x_1378_;
v_isShared_1382_ = v_isSharedCheck_1415_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1378_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1415_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_a_1379_, v_e_1355_);
lean_dec(v_a_1379_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v___x_1384_; 
lean_del_object(v___x_1381_);
lean_inc_ref(v_fn_1354_);
lean_inc(v___y_1360_);
lean_inc_ref(v___y_1359_);
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc_ref(v_e_1355_);
v___x_1384_ = lean_apply_6(v_fn_1354_, v_e_1355_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, lean_box(0));
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; uint8_t v___x_1386_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1386_ = lean_unbox(v_a_1385_);
lean_dec(v_a_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; 
lean_dec_ref(v_fn_1354_);
v___x_1387_ = lean_box(0);
v_a_1363_ = v___x_1387_;
goto v___jp_1362_;
}
else
{
switch(lean_obj_tag(v_e_1355_))
{
case 7:
{
lean_object* v___f_1388_; lean_object* v___x_1389_; 
v___f_1388_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1388_, 0, v_fn_1354_);
lean_inc_ref(v_e_1355_);
v___x_1389_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(v___f_1388_, v_e_1355_, v_a_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
v___y_1375_ = v___x_1389_;
goto v___jp_1374_;
}
case 6:
{
lean_object* v___f_1390_; lean_object* v___x_1391_; 
v___f_1390_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1390_, 0, v_fn_1354_);
lean_inc_ref(v_e_1355_);
v___x_1391_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(v___f_1390_, v_e_1355_, v_a_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
v___y_1375_ = v___x_1391_;
goto v___jp_1374_;
}
case 8:
{
lean_object* v___f_1392_; lean_object* v___x_1393_; 
v___f_1392_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1392_, 0, v_fn_1354_);
lean_inc_ref(v_e_1355_);
v___x_1393_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(v___f_1392_, v_e_1355_, v_a_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
v___y_1375_ = v___x_1393_;
goto v___jp_1374_;
}
case 5:
{
lean_object* v_fn_1394_; lean_object* v_arg_1395_; lean_object* v___x_1396_; 
v_fn_1394_ = lean_ctor_get(v_e_1355_, 0);
v_arg_1395_ = lean_ctor_get(v_e_1355_, 1);
lean_inc_ref(v_fn_1394_);
lean_inc_ref(v_fn_1354_);
v___x_1396_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1354_, v_fn_1394_, v_a_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v___x_1397_; 
lean_dec_ref_known(v___x_1396_, 1);
lean_inc_ref(v_arg_1395_);
v___x_1397_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1354_, v_arg_1395_, v_a_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
v___y_1375_ = v___x_1397_;
goto v___jp_1374_;
}
else
{
lean_dec_ref(v_fn_1354_);
v___y_1375_ = v___x_1396_;
goto v___jp_1374_;
}
}
case 10:
{
lean_object* v_expr_1398_; lean_object* v___x_1399_; 
v_expr_1398_ = lean_ctor_get(v_e_1355_, 1);
lean_inc_ref(v_expr_1398_);
v___x_1399_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1354_, v_expr_1398_, v_a_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
v___y_1375_ = v___x_1399_;
goto v___jp_1374_;
}
case 11:
{
lean_object* v_struct_1400_; lean_object* v___x_1401_; 
v_struct_1400_ = lean_ctor_get(v_e_1355_, 2);
lean_inc_ref(v_struct_1400_);
v___x_1401_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1354_, v_struct_1400_, v_a_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
v___y_1375_ = v___x_1401_;
goto v___jp_1374_;
}
default: 
{
lean_object* v___x_1402_; 
lean_dec_ref(v_fn_1354_);
v___x_1402_ = lean_box(0);
v_a_1363_ = v___x_1402_;
goto v___jp_1362_;
}
}
}
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_dec_ref(v_e_1355_);
lean_dec_ref(v_fn_1354_);
v_a_1403_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1384_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1384_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
else
{
lean_object* v_val_1411_; lean_object* v___x_1413_; 
lean_dec_ref(v_e_1355_);
lean_dec_ref(v_fn_1354_);
v_val_1411_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_val_1411_);
lean_dec_ref_known(v___x_1383_, 1);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v_val_1411_);
v___x_1413_ = v___x_1381_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_val_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec_ref(v_e_1355_);
lean_dec_ref(v_fn_1354_);
v_a_1416_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1378_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1378_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
v___jp_1362_:
{
lean_object* v___f_1364_; lean_object* v___x_1365_; 
lean_inc(v_a_1356_);
v___f_1364_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1364_, 0, v_a_1356_);
lean_closure_set(v___f_1364_, 1, v_e_1355_);
lean_closure_set(v___f_1364_, 2, v_a_1363_);
v___x_1365_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_box(0), v___f_1364_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1372_ == 0)
{
lean_object* v_unused_1373_; 
v_unused_1373_ = lean_ctor_get(v___x_1365_, 0);
lean_dec(v_unused_1373_);
v___x_1367_ = v___x_1365_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_dec(v___x_1365_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v_a_1363_);
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1363_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
else
{
return v___x_1365_;
}
}
v___jp_1374_:
{
if (lean_obj_tag(v___y_1375_) == 0)
{
lean_object* v_a_1376_; 
v_a_1376_ = lean_ctor_get(v___y_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___y_1375_, 1);
v_a_1363_ = v_a_1376_;
goto v___jp_1362_;
}
else
{
lean_dec_ref(v_e_1355_);
return v___y_1375_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2(lean_object* v_fn_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___boxed(lean_object* v_fn_1433_, lean_object* v_e_1434_, lean_object* v_a_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1433_, v_e_1434_, v_a_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v_a_1435_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_object* v_00_u03b1_1442_, lean_object* v_x_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = lean_apply_1(v_x_1443_, lean_box(0));
v___x_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0___boxed(lean_object* v_00_u03b1_1451_, lean_object* v_x_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(v_00_u03b1_1451_, v_x_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(lean_object* v_input_1459_, lean_object* v_fn_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v_a_1468_; lean_object* v___x_1469_; 
v___x_1466_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___redArg___closed__2, &l_Lean_Meta_forEachExpr_x27___redArg___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__2);
v___x_1467_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_box(0), v___x_1466_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1468_);
lean_dec_ref(v___x_1467_);
v___x_1469_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1460_, v_input_1459_, v_a_1468_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___x_1469_, 1);
v___x_1471_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1471_, 0, lean_box(0));
lean_closure_set(v___x_1471_, 1, lean_box(0));
lean_closure_set(v___x_1471_, 2, v_a_1468_);
v___x_1472_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_box(0), v___x_1471_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; 
v_unused_1480_ = lean_ctor_get(v___x_1472_, 0);
lean_dec(v_unused_1480_);
v___x_1474_ = v___x_1472_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_dec(v___x_1472_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 0, v_a_1470_);
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1470_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
else
{
lean_dec(v_a_1468_);
return v___x_1469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___boxed(lean_object* v_input_1481_, lean_object* v_fn_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(v_input_1481_, v_fn_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0(lean_object* v_f_1489_, lean_object* v_e_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v___x_1496_; 
lean_inc(v___y_1494_);
lean_inc_ref(v___y_1493_);
lean_inc(v___y_1492_);
lean_inc_ref(v___y_1491_);
v___x_1496_ = lean_apply_6(v_f_1489_, v_e_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, lean_box(0));
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1505_; 
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v___x_1496_, 0);
lean_dec(v_unused_1506_);
v___x_1498_ = v___x_1496_;
v_isShared_1499_ = v_isSharedCheck_1505_;
goto v_resetjp_1497_;
}
else
{
lean_dec(v___x_1496_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1505_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
uint8_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1500_ = 1;
v___x_1501_ = lean_box(v___x_1500_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 0, v___x_1501_);
v___x_1503_ = v___x_1498_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
else
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
v_a_1507_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1496_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1496_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0___boxed(lean_object* v_f_1515_, lean_object* v_e_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0(v_f_1515_, v_e_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(lean_object* v_e_1523_, lean_object* v_f_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___f_1530_; lean_object* v___x_1531_; 
v___f_1530_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1530_, 0, v_f_1524_);
v___x_1531_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(v_e_1523_, v___f_1530_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___boxed(lean_object* v_e_1532_, lean_object* v_f_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(v_e_1532_, v_f_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt(lean_object* v_e_1542_, lean_object* v_isTarget_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v_a_1553_; lean_object* v___f_1554_; lean_object* v___x_1555_; 
v___x_1549_ = lean_unsigned_to_nat(0u);
v___x_1550_ = ((lean_object*)(l_Lean_Meta_setMVarUserNamesAt___closed__0));
v___x_1551_ = lean_st_mk_ref(v___x_1550_);
v___x_1552_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(v_e_1542_, v_a_1545_);
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref(v___x_1552_);
lean_inc(v___x_1551_);
v___f_1554_ = lean_alloc_closure((void*)(l_Lean_Meta_setMVarUserNamesAt___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1554_, 0, v___x_1551_);
lean_closure_set(v___f_1554_, 1, v_isTarget_1543_);
lean_closure_set(v___f_1554_, 2, v___x_1549_);
v___x_1555_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(v_a_1553_, v___f_1554_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1563_; 
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1563_ == 0)
{
lean_object* v_unused_1564_; 
v_unused_1564_ = lean_ctor_get(v___x_1555_, 0);
lean_dec(v_unused_1564_);
v___x_1557_ = v___x_1555_;
v_isShared_1558_ = v_isSharedCheck_1563_;
goto v_resetjp_1556_;
}
else
{
lean_dec(v___x_1555_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1563_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1559_; lean_object* v___x_1561_; 
v___x_1559_ = lean_st_ref_get(v___x_1551_);
lean_dec(v___x_1551_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 0, v___x_1559_);
v___x_1561_ = v___x_1557_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v___x_1551_);
v_a_1565_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1555_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1555_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___boxed(lean_object* v_e_1573_, lean_object* v_isTarget_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_Meta_setMVarUserNamesAt(v_e_1573_, v_isTarget_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_);
lean_dec(v_a_1578_);
lean_dec_ref(v_a_1577_);
lean_dec(v_a_1576_);
lean_dec_ref(v_a_1575_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2(lean_object* v_upperBound_1581_, lean_object* v___x_1582_, lean_object* v_val_1583_, lean_object* v_e_1584_, lean_object* v_isTarget_1585_, lean_object* v_inst_1586_, lean_object* v_R_1587_, lean_object* v_a_1588_, lean_object* v_b_1589_, lean_object* v_c_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(v_upperBound_1581_, v___x_1582_, v_val_1583_, v_e_1584_, v_isTarget_1585_, v_a_1588_, v_b_1589_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___boxed(lean_object* v_upperBound_1597_, lean_object* v___x_1598_, lean_object* v_val_1599_, lean_object* v_e_1600_, lean_object* v_isTarget_1601_, lean_object* v_inst_1602_, lean_object* v_R_1603_, lean_object* v_a_1604_, lean_object* v_b_1605_, lean_object* v_c_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2(v_upperBound_1597_, v___x_1598_, v_val_1599_, v_e_1600_, v_isTarget_1601_, v_inst_1602_, v_R_1603_, v_a_1604_, v_b_1605_, v_c_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec_ref(v_isTarget_1601_);
lean_dec_ref(v_e_1600_);
lean_dec_ref(v___x_1598_);
lean_dec(v_upperBound_1597_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_1613_, lean_object* v_m_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_m_1614_, v_a_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___boxed(lean_object* v_00_u03b2_1617_, lean_object* v_m_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7(v_00_u03b2_1617_, v_m_1618_, v_a_1619_);
lean_dec_ref(v_a_1619_);
lean_dec_ref(v_m_1618_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_1621_, lean_object* v_m_1622_, lean_object* v_a_1623_, lean_object* v_b_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(v_m_1622_, v_a_1623_, v_b_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_1626_, lean_object* v_a_1627_, lean_object* v_x_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(v_a_1627_, v_x_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03b2_1630_, lean_object* v_a_1631_, lean_object* v_x_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8(v_00_u03b2_1630_, v_a_1631_, v_x_1632_);
lean_dec(v_x_1632_);
lean_dec_ref(v_a_1631_);
return v_res_1633_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_1634_, lean_object* v_a_1635_, lean_object* v_x_1636_){
_start:
{
uint8_t v___x_1637_; 
v___x_1637_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_a_1635_, v_x_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b2_1638_, lean_object* v_a_1639_, lean_object* v_x_1640_){
_start:
{
uint8_t v_res_1641_; lean_object* v_r_1642_; 
v_res_1641_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10(v_00_u03b2_1638_, v_a_1639_, v_x_1640_);
lean_dec(v_x_1640_);
lean_dec_ref(v_a_1639_);
v_r_1642_ = lean_box(v_res_1641_);
return v_r_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11(lean_object* v_00_u03b2_1643_, lean_object* v_data_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11___redArg(v_data_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12(lean_object* v_00_u03b2_1646_, lean_object* v_a_1647_, lean_object* v_b_1648_, lean_object* v_x_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(v_a_1647_, v_b_1648_, v_x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16(lean_object* v_00_u03b1_1651_, lean_object* v_name_1652_, uint8_t v_bi_1653_, lean_object* v_type_1654_, lean_object* v_k_1655_, uint8_t v_kind_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_name_1652_, v_bi_1653_, v_type_1654_, v_k_1655_, v_kind_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1664_, lean_object* v_name_1665_, lean_object* v_bi_1666_, lean_object* v_type_1667_, lean_object* v_k_1668_, lean_object* v_kind_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
uint8_t v_bi_boxed_1676_; uint8_t v_kind_boxed_1677_; lean_object* v_res_1678_; 
v_bi_boxed_1676_ = lean_unbox(v_bi_1666_);
v_kind_boxed_1677_ = lean_unbox(v_kind_1669_);
v_res_1678_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16(v_00_u03b1_1664_, v_name_1665_, v_bi_boxed_1676_, v_type_1667_, v_k_1668_, v_kind_boxed_1677_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21(lean_object* v_00_u03b1_1679_, lean_object* v_name_1680_, lean_object* v_type_1681_, lean_object* v_val_1682_, lean_object* v_k_1683_, uint8_t v_nondep_1684_, uint8_t v_kind_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(v_name_1680_, v_type_1681_, v_val_1682_, v_k_1683_, v_nondep_1684_, v_kind_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___boxed(lean_object* v_00_u03b1_1693_, lean_object* v_name_1694_, lean_object* v_type_1695_, lean_object* v_val_1696_, lean_object* v_k_1697_, lean_object* v_nondep_1698_, lean_object* v_kind_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
uint8_t v_nondep_boxed_1706_; uint8_t v_kind_boxed_1707_; lean_object* v_res_1708_; 
v_nondep_boxed_1706_ = lean_unbox(v_nondep_1698_);
v_kind_boxed_1707_ = lean_unbox(v_kind_1699_);
v_res_1708_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21(v_00_u03b1_1693_, v_name_1694_, v_type_1695_, v_val_1696_, v_k_1697_, v_nondep_boxed_1706_, v_kind_boxed_1707_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_1709_, lean_object* v_i_1710_, lean_object* v_source_1711_, lean_object* v_target_1712_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12___redArg(v_i_1710_, v_source_1711_, v_target_1712_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16(lean_object* v_00_u03b2_1714_, lean_object* v_x_1715_, lean_object* v_x_1716_){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16___redArg(v_x_1715_, v_x_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(lean_object* v_as_1718_, size_t v_sz_1719_, size_t v_i_1720_, lean_object* v_b_1721_, lean_object* v___y_1722_){
_start:
{
uint8_t v___x_1724_; 
v___x_1724_ = lean_usize_dec_lt(v_i_1720_, v_sz_1719_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v_b_1721_);
return v___x_1725_;
}
else
{
lean_object* v___x_1726_; lean_object* v_mctx_1727_; lean_object* v_cache_1728_; lean_object* v_zetaDeltaFVarIds_1729_; lean_object* v_postponed_1730_; lean_object* v_diag_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1746_; 
v___x_1726_ = lean_st_ref_take(v___y_1722_);
v_mctx_1727_ = lean_ctor_get(v___x_1726_, 0);
v_cache_1728_ = lean_ctor_get(v___x_1726_, 1);
v_zetaDeltaFVarIds_1729_ = lean_ctor_get(v___x_1726_, 2);
v_postponed_1730_ = lean_ctor_get(v___x_1726_, 3);
v_diag_1731_ = lean_ctor_get(v___x_1726_, 4);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1733_ = v___x_1726_;
v_isShared_1734_ = v_isSharedCheck_1746_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_diag_1731_);
lean_inc(v_postponed_1730_);
lean_inc(v_zetaDeltaFVarIds_1729_);
lean_inc(v_cache_1728_);
lean_inc(v_mctx_1727_);
lean_dec(v___x_1726_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1746_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v_a_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
v_a_1735_ = lean_array_uget_borrowed(v_as_1718_, v_i_1720_);
v___x_1736_ = lean_box(0);
lean_inc(v_a_1735_);
v___x_1737_ = l_Lean_MetavarContext_setMVarUserNameTemporarily(v_mctx_1727_, v_a_1735_, v___x_1736_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 0, v___x_1737_);
v___x_1739_ = v___x_1733_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1737_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_cache_1728_);
lean_ctor_set(v_reuseFailAlloc_1745_, 2, v_zetaDeltaFVarIds_1729_);
lean_ctor_set(v_reuseFailAlloc_1745_, 3, v_postponed_1730_);
lean_ctor_set(v_reuseFailAlloc_1745_, 4, v_diag_1731_);
v___x_1739_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; size_t v___x_1742_; size_t v___x_1743_; 
v___x_1740_ = lean_st_ref_set(v___y_1722_, v___x_1739_);
v___x_1741_ = lean_box(0);
v___x_1742_ = ((size_t)1ULL);
v___x_1743_ = lean_usize_add(v_i_1720_, v___x_1742_);
v_i_1720_ = v___x_1743_;
v_b_1721_ = v___x_1741_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg___boxed(lean_object* v_as_1747_, lean_object* v_sz_1748_, lean_object* v_i_1749_, lean_object* v_b_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
size_t v_sz_boxed_1753_; size_t v_i_boxed_1754_; lean_object* v_res_1755_; 
v_sz_boxed_1753_ = lean_unbox_usize(v_sz_1748_);
lean_dec(v_sz_1748_);
v_i_boxed_1754_ = lean_unbox_usize(v_i_1749_);
lean_dec(v_i_1749_);
v_res_1755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_as_1747_, v_sz_boxed_1753_, v_i_boxed_1754_, v_b_1750_, v___y_1751_);
lean_dec(v___y_1751_);
lean_dec_ref(v_as_1747_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_resetMVarUserNames(lean_object* v_toReset_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v___x_1762_; size_t v_sz_1763_; size_t v___x_1764_; lean_object* v___x_1765_; 
v___x_1762_ = lean_box(0);
v_sz_1763_ = lean_array_size(v_toReset_1756_);
v___x_1764_ = ((size_t)0ULL);
v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_toReset_1756_, v_sz_1763_, v___x_1764_, v___x_1762_, v_a_1758_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1772_ == 0)
{
lean_object* v_unused_1773_; 
v_unused_1773_ = lean_ctor_get(v___x_1765_, 0);
lean_dec(v_unused_1773_);
v___x_1767_ = v___x_1765_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_dec(v___x_1765_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1762_);
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1762_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
else
{
return v___x_1765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_resetMVarUserNames___boxed(lean_object* v_toReset_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_Meta_resetMVarUserNames(v_toReset_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_);
lean_dec(v_a_1778_);
lean_dec_ref(v_a_1777_);
lean_dec(v_a_1776_);
lean_dec_ref(v_a_1775_);
lean_dec_ref(v_toReset_1774_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0(lean_object* v_as_1781_, size_t v_sz_1782_, size_t v_i_1783_, lean_object* v_b_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_as_1781_, v_sz_1782_, v_i_1783_, v_b_1784_, v___y_1786_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___boxed(lean_object* v_as_1791_, lean_object* v_sz_1792_, lean_object* v_i_1793_, lean_object* v_b_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
size_t v_sz_boxed_1800_; size_t v_i_boxed_1801_; lean_object* v_res_1802_; 
v_sz_boxed_1800_ = lean_unbox_usize(v_sz_1792_);
lean_dec(v_sz_1792_);
v_i_boxed_1801_ = lean_unbox_usize(v_i_1793_);
lean_dec(v_i_1793_);
v_res_1802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0(v_as_1791_, v_sz_boxed_1800_, v_i_boxed_1801_, v_b_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec_ref(v_as_1791_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(lean_object* v_x_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
if (lean_obj_tag(v_x_1803_) == 2)
{
lean_object* v_mvarId_1809_; lean_object* v___x_1810_; 
v_mvarId_1809_ = lean_ctor_get(v_x_1803_, 0);
lean_inc(v_mvarId_1809_);
lean_dec_ref_known(v_x_1803_, 1);
v___x_1810_ = l_Lean_MVarId_getDecl(v_mvarId_1809_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1821_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1821_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1821_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v_userName_1815_; uint8_t v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1819_; 
v_userName_1815_ = lean_ctor_get(v_a_1811_, 0);
lean_inc(v_userName_1815_);
lean_dec(v_a_1811_);
v___x_1816_ = l_Lean_Name_isAnonymous(v_userName_1815_);
lean_dec(v_userName_1815_);
v___x_1817_ = lean_box(v___x_1816_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1817_);
v___x_1819_ = v___x_1813_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
v_a_1822_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1810_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1810_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
else
{
uint8_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_dec_ref(v_x_1803_);
v___x_1830_ = 0;
v___x_1831_ = lean_box(v___x_1830_);
v___x_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
return v___x_1832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0___boxed(lean_object* v_x_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(v_x_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__0(lean_object* v_val_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_x3f_1845_){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = lean_st_ref_get(v_val_1840_);
v___x_1848_ = l_Lean_Meta_resetMVarUserNames(v___x_1847_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
lean_dec(v___x_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__0___boxed(lean_object* v_val_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_x3f_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_Meta_mkForallFVars_x27___lam__0(v_val_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_x3f_1854_);
lean_dec(v_a_x3f_1854_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
lean_dec(v_val_1849_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(lean_object* v_xs_1857_, lean_object* v_as_1858_, size_t v_sz_1859_, size_t v_i_1860_, lean_object* v_b_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
uint8_t v___x_1868_; 
v___x_1868_ = lean_usize_dec_lt(v_i_1860_, v_sz_1859_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; 
lean_dec_ref(v_xs_1857_);
v___x_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1869_, 0, v_b_1861_);
return v___x_1869_;
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1871_; 
v_a_1870_ = lean_array_uget_borrowed(v_as_1858_, v_i_1860_);
lean_inc(v___y_1866_);
lean_inc_ref(v___y_1865_);
lean_inc(v___y_1864_);
lean_inc_ref(v___y_1863_);
lean_inc(v_a_1870_);
v___x_1871_ = lean_infer_type(v_a_1870_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1873_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___x_1871_, 1);
lean_inc_ref(v_xs_1857_);
v___x_1873_ = l_Lean_Meta_setMVarUserNamesAt(v_a_1872_, v_xs_1857_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; size_t v___x_1879_; size_t v___x_1880_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_a_1874_);
lean_dec_ref_known(v___x_1873_, 1);
v___x_1875_ = lean_st_ref_take(v___y_1862_);
v___x_1876_ = l_Array_append___redArg(v___x_1875_, v_a_1874_);
lean_dec(v_a_1874_);
v___x_1877_ = lean_st_ref_set(v___y_1862_, v___x_1876_);
v___x_1878_ = lean_box(0);
v___x_1879_ = ((size_t)1ULL);
v___x_1880_ = lean_usize_add(v_i_1860_, v___x_1879_);
v_i_1860_ = v___x_1880_;
v_b_1861_ = v___x_1878_;
goto _start;
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec_ref(v_xs_1857_);
v_a_1882_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1873_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1873_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
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
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec_ref(v_xs_1857_);
v_a_1890_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1871_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1871_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2___boxed(lean_object* v_xs_1898_, lean_object* v_as_1899_, lean_object* v_sz_1900_, lean_object* v_i_1901_, lean_object* v_b_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
size_t v_sz_boxed_1909_; size_t v_i_boxed_1910_; lean_object* v_res_1911_; 
v_sz_boxed_1909_ = lean_unbox_usize(v_sz_1900_);
lean_dec(v_sz_1900_);
v_i_boxed_1910_ = lean_unbox_usize(v_i_1901_);
lean_dec(v_i_1901_);
v_res_1911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(v_xs_1898_, v_as_1899_, v_sz_boxed_1909_, v_i_boxed_1910_, v_b_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v_as_1899_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(lean_object* v_xs_1912_, lean_object* v_as_1913_, size_t v_sz_1914_, size_t v_i_1915_, lean_object* v_b_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
uint8_t v___x_1923_; 
v___x_1923_ = lean_usize_dec_lt(v_i_1915_, v_sz_1914_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; 
lean_dec_ref(v_xs_1912_);
v___x_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1924_, 0, v_b_1916_);
return v___x_1924_;
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1926_; 
v_a_1925_ = lean_array_uget_borrowed(v_as_1913_, v_i_1915_);
lean_inc(v___y_1921_);
lean_inc_ref(v___y_1920_);
lean_inc(v___y_1919_);
lean_inc_ref(v___y_1918_);
lean_inc(v_a_1925_);
v___x_1926_ = lean_infer_type(v_a_1925_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___x_1928_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___x_1926_, 1);
lean_inc_ref(v_xs_1912_);
v___x_1928_ = l_Lean_Meta_setMVarUserNamesAt(v_a_1927_, v_xs_1912_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; size_t v___x_1934_; size_t v___x_1935_; lean_object* v___x_1936_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v___x_1928_, 1);
v___x_1930_ = lean_st_ref_take(v___y_1917_);
v___x_1931_ = l_Array_append___redArg(v___x_1930_, v_a_1929_);
lean_dec(v_a_1929_);
v___x_1932_ = lean_st_ref_set(v___y_1917_, v___x_1931_);
v___x_1933_ = lean_box(0);
v___x_1934_ = ((size_t)1ULL);
v___x_1935_ = lean_usize_add(v_i_1915_, v___x_1934_);
v___x_1936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(v_xs_1912_, v_as_1913_, v_sz_1914_, v___x_1935_, v___x_1933_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
return v___x_1936_;
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec_ref(v_xs_1912_);
v_a_1937_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1928_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1928_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec_ref(v_xs_1912_);
v_a_1945_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1926_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1926_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2___boxed(lean_object* v_xs_1953_, lean_object* v_as_1954_, lean_object* v_sz_1955_, lean_object* v_i_1956_, lean_object* v_b_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
size_t v_sz_boxed_1964_; size_t v_i_boxed_1965_; lean_object* v_res_1966_; 
v_sz_boxed_1964_ = lean_unbox_usize(v_sz_1955_);
lean_dec(v_sz_1955_);
v_i_boxed_1965_ = lean_unbox_usize(v_i_1956_);
lean_dec(v_i_1956_);
v_res_1966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(v_xs_1953_, v_as_1954_, v_sz_boxed_1964_, v_i_boxed_1965_, v_b_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v_as_1954_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(lean_object* v_as_1967_, size_t v_i_1968_, size_t v_stop_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
uint8_t v___x_1975_; 
v___x_1975_ = lean_usize_dec_eq(v_i_1968_, v_stop_1969_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = lean_array_uget_borrowed(v_as_1967_, v_i_1968_);
lean_inc(v___x_1976_);
v___x_1977_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(v___x_1976_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1989_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_1989_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1989_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
uint8_t v___x_1982_; 
v___x_1982_ = lean_unbox(v_a_1978_);
if (v___x_1982_ == 0)
{
size_t v___x_1983_; size_t v___x_1984_; 
lean_del_object(v___x_1980_);
lean_dec(v_a_1978_);
v___x_1983_ = ((size_t)1ULL);
v___x_1984_ = lean_usize_add(v_i_1968_, v___x_1983_);
v_i_1968_ = v___x_1984_;
goto _start;
}
else
{
lean_object* v___x_1987_; 
if (v_isShared_1981_ == 0)
{
v___x_1987_ = v___x_1980_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1978_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
else
{
return v___x_1977_;
}
}
else
{
uint8_t v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = 0;
v___x_1991_ = lean_box(v___x_1990_);
v___x_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
return v___x_1992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1___boxed(lean_object* v_as_1993_, lean_object* v_i_1994_, lean_object* v_stop_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
size_t v_i_boxed_2001_; size_t v_stop_boxed_2002_; lean_object* v_res_2003_; 
v_i_boxed_2001_ = lean_unbox_usize(v_i_1994_);
lean_dec(v_i_1994_);
v_stop_boxed_2002_ = lean_unbox_usize(v_stop_1995_);
lean_dec(v_stop_1995_);
v_res_2003_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(v_as_1993_, v_i_boxed_2001_, v_stop_boxed_2002_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec_ref(v_as_1993_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27(lean_object* v_xs_2004_, lean_object* v_type_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
uint8_t v_a_2012_; lean_object* v___x_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2016_ = lean_unsigned_to_nat(0u);
v___x_2017_ = lean_array_get_size(v_xs_2004_);
v___x_2018_ = lean_nat_dec_lt(v___x_2016_, v___x_2017_);
if (v___x_2018_ == 0)
{
v_a_2012_ = v___x_2018_;
goto v___jp_2011_;
}
else
{
if (v___x_2018_ == 0)
{
v_a_2012_ = v___x_2018_;
goto v___jp_2011_;
}
else
{
size_t v___x_2019_; size_t v___x_2020_; lean_object* v___x_2021_; 
v___x_2019_ = ((size_t)0ULL);
v___x_2020_ = lean_usize_of_nat(v___x_2017_);
v___x_2021_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(v_xs_2004_, v___x_2019_, v___x_2020_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; uint8_t v___x_2023_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2023_ = lean_unbox(v_a_2022_);
if (v___x_2023_ == 0)
{
uint8_t v___x_2024_; 
v___x_2024_ = lean_unbox(v_a_2022_);
lean_dec(v_a_2022_);
v_a_2012_ = v___x_2024_;
goto v___jp_2011_;
}
else
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v_a_2028_; lean_object* v___x_2047_; size_t v_sz_2048_; lean_object* v___x_2049_; 
lean_dec(v_a_2022_);
v___x_2025_ = ((lean_object*)(l_Lean_Meta_setMVarUserNamesAt___closed__0));
v___x_2026_ = lean_st_mk_ref(v___x_2025_);
v___x_2047_ = lean_box(0);
v_sz_2048_ = lean_array_size(v_xs_2004_);
lean_inc_ref(v_xs_2004_);
v___x_2049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(v_xs_2004_, v_xs_2004_, v_sz_2048_, v___x_2019_, v___x_2047_, v___x_2026_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v___x_2050_; 
lean_dec_ref_known(v___x_2049_, 1);
lean_inc_ref(v_xs_2004_);
lean_inc_ref(v_type_2005_);
v___x_2050_ = l_Lean_Meta_setMVarUserNamesAt(v_type_2005_, v_xs_2004_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref_known(v___x_2050_, 1);
v___x_2052_ = lean_st_ref_take(v___x_2026_);
v___x_2053_ = l_Array_append___redArg(v___x_2052_, v_a_2051_);
lean_dec(v_a_2051_);
v___x_2054_ = lean_st_ref_set(v___x_2026_, v___x_2053_);
v___x_2055_ = 0;
v___x_2056_ = 1;
v___x_2057_ = l_Lean_Meta_mkForallFVars(v_xs_2004_, v_type_2005_, v___x_2055_, v___x_2018_, v___x_2018_, v___x_2056_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_);
lean_dec_ref(v_xs_2004_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2083_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2083_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2083_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
lean_inc(v_a_2058_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set_tag(v___x_2060_, 1);
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2064_; 
v___x_2064_ = l_Lean_Meta_mkForallFVars_x27___lam__0(v___x_2026_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v___x_2063_);
lean_dec_ref(v___x_2063_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2072_; 
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; 
v_unused_2073_ = lean_ctor_get(v___x_2064_, 0);
lean_dec(v_unused_2073_);
v___x_2066_ = v___x_2064_;
v_isShared_2067_ = v_isSharedCheck_2072_;
goto v_resetjp_2065_;
}
else
{
lean_dec(v___x_2064_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2072_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
v___x_2068_ = lean_st_ref_get(v___x_2026_);
lean_dec(v___x_2026_);
lean_dec(v___x_2068_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v_a_2058_);
v___x_2070_ = v___x_2066_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2058_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec(v_a_2058_);
lean_dec(v___x_2026_);
v_a_2074_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2064_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2064_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
}
}
else
{
lean_object* v_a_2084_; 
v_a_2084_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2084_);
lean_dec_ref_known(v___x_2057_, 1);
v_a_2028_ = v_a_2084_;
goto v___jp_2027_;
}
}
else
{
lean_object* v_a_2085_; 
lean_dec_ref(v_type_2005_);
lean_dec_ref(v_xs_2004_);
v_a_2085_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2085_);
lean_dec_ref_known(v___x_2050_, 1);
v_a_2028_ = v_a_2085_;
goto v___jp_2027_;
}
}
else
{
lean_object* v_a_2086_; 
lean_dec_ref(v_type_2005_);
lean_dec_ref(v_xs_2004_);
v_a_2086_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2049_, 1);
v_a_2028_ = v_a_2086_;
goto v___jp_2027_;
}
v___jp_2027_:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = lean_box(0);
v___x_2030_ = l_Lean_Meta_mkForallFVars_x27___lam__0(v___x_2026_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v___x_2029_);
lean_dec(v___x_2026_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2037_ == 0)
{
lean_object* v_unused_2038_; 
v_unused_2038_ = lean_ctor_get(v___x_2030_, 0);
lean_dec(v_unused_2038_);
v___x_2032_ = v___x_2030_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_dec(v___x_2030_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set_tag(v___x_2032_, 1);
lean_ctor_set(v___x_2032_, 0, v_a_2028_);
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2028_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec_ref(v_a_2028_);
v_a_2039_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2030_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2030_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec_ref(v_type_2005_);
lean_dec_ref(v_xs_2004_);
v_a_2087_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2021_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2021_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
}
v___jp_2011_:
{
uint8_t v___x_2013_; uint8_t v___x_2014_; lean_object* v___x_2015_; 
v___x_2013_ = 1;
v___x_2014_ = 1;
v___x_2015_ = l_Lean_Meta_mkForallFVars(v_xs_2004_, v_type_2005_, v_a_2012_, v___x_2013_, v___x_2013_, v___x_2014_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_);
lean_dec_ref(v_xs_2004_);
return v___x_2015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___boxed(lean_object* v_xs_2095_, lean_object* v_type_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_Meta_mkForallFVars_x27(v_xs_2095_, v_type_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
return v_res_2102_;
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
