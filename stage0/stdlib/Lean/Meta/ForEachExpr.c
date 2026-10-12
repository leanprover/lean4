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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_binderName_3_, uint8_t v_binderInfo_4_, lean_object* v_d_5_, lean_object* v___f_6_, lean_object* v_____r_7_){
_start:
{
uint8_t v___x_8_; lean_object* v___x_9_; 
v___x_8_ = 0;
v___x_9_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1_, v_inst_2_, v_binderName_3_, v_binderInfo_4_, v_d_5_, v___f_6_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1_ = stack[0].m_obj;
lean_object* v_inst_2_ = stack[1].m_obj;
lean_object* v_binderName_3_ = stack[2].m_obj;
uint8_t v_binderInfo_4_ = stack[3].m_num;
lean_object* v_d_5_ = stack[4].m_obj;
lean_object* v___f_6_ = stack[5].m_obj;
lean_object* v_____r_7_ = stack[6].m_obj;
lean_object* v_res_10_;
v_res_10_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1(v_inst_1_, v_inst_2_, v_binderName_3_, v_binderInfo_4_, v_d_5_, v___f_6_, v_____r_7_);
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1___boxed(lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_binderName_13_, lean_object* v_binderInfo_14_, lean_object* v_d_15_, lean_object* v___f_16_, lean_object* v_____r_17_){
_start:
{
uint8_t v_binderInfo_63__boxed_18_; lean_object* v_res_19_; 
v_binderInfo_63__boxed_18_ = lean_unbox(v_binderInfo_14_);
v_res_19_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1(v_inst_11_, v_inst_12_, v_binderName_13_, v_binderInfo_63__boxed_18_, v_d_15_, v___f_16_, v_____r_17_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg(lean_object* v_inst_20_, lean_object* v_inst_21_, lean_object* v_f_22_, lean_object* v_fvars_23_, lean_object* v_a_24_){
_start:
{
if (lean_obj_tag(v_a_24_) == 6)
{
lean_object* v_toBind_25_; lean_object* v_binderName_26_; lean_object* v_binderType_27_; lean_object* v_body_28_; uint8_t v_binderInfo_29_; lean_object* v___f_30_; lean_object* v_d_31_; lean_object* v___x_32_; lean_object* v___f_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v_toBind_25_ = lean_ctor_get(v_inst_20_, 1);
lean_inc(v_toBind_25_);
v_binderName_26_ = lean_ctor_get(v_a_24_, 0);
lean_inc(v_binderName_26_);
v_binderType_27_ = lean_ctor_get(v_a_24_, 1);
lean_inc_ref(v_binderType_27_);
v_body_28_ = lean_ctor_get(v_a_24_, 2);
lean_inc_ref(v_body_28_);
v_binderInfo_29_ = lean_ctor_get_uint8(v_a_24_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_24_, 3);
lean_inc(v_f_22_);
lean_inc_ref(v_inst_21_);
lean_inc_ref(v_inst_20_);
lean_inc_ref(v_fvars_23_);
v___f_30_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__0), 6, 5);
lean_closure_set(v___f_30_, 0, v_fvars_23_);
lean_closure_set(v___f_30_, 1, v_inst_20_);
lean_closure_set(v___f_30_, 2, v_inst_21_);
lean_closure_set(v___f_30_, 3, v_f_22_);
lean_closure_set(v___f_30_, 4, v_body_28_);
v_d_31_ = lean_expr_instantiate_rev(v_binderType_27_, v_fvars_23_);
lean_dec_ref(v_fvars_23_);
lean_dec_ref(v_binderType_27_);
v___x_32_ = lean_box(v_binderInfo_29_);
lean_inc_ref(v_d_31_);
v___f_33_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_33_, 0, v_inst_21_);
lean_closure_set(v___f_33_, 1, v_inst_20_);
lean_closure_set(v___f_33_, 2, v_binderName_26_);
lean_closure_set(v___f_33_, 3, v___x_32_);
lean_closure_set(v___f_33_, 4, v_d_31_);
lean_closure_set(v___f_33_, 5, v___f_30_);
v___x_34_ = lean_apply_1(v_f_22_, v_d_31_);
v___x_35_ = lean_apply_4(v_toBind_25_, lean_box(0), lean_box(0), v___x_34_, v___f_33_);
return v___x_35_;
}
else
{
lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec_ref(v_inst_21_);
lean_dec_ref(v_inst_20_);
v___x_36_ = lean_expr_instantiate_rev(v_a_24_, v_fvars_23_);
lean_dec_ref(v_fvars_23_);
lean_dec_ref(v_a_24_);
v___x_37_ = lean_apply_1(v_f_22_, v___x_36_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__0(lean_object* v_fvars_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_f_41_, lean_object* v_body_42_, lean_object* v_x_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_array_push(v_fvars_38_, v_x_43_);
v___x_45_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg(v_inst_39_, v_inst_40_, v_f_41_, v___x_44_, v_body_42_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit(lean_object* v_m_46_, lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_f_49_, lean_object* v_fvars_50_, lean_object* v_a_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg(v_inst_47_, v_inst_48_, v_f_49_, v_fvars_50_, v_a_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___redArg(lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_f_57_, lean_object* v_e_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_60_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg(v_inst_55_, v_inst_56_, v_f_57_, v___x_59_, v_e_58_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda(lean_object* v_m_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_f_64_, lean_object* v_e_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Meta_visitLambda___redArg(v_inst_62_, v_inst_63_, v_f_64_, v_e_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg(lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_f_69_, lean_object* v_fvars_70_, lean_object* v_a_71_){
_start:
{
if (lean_obj_tag(v_a_71_) == 7)
{
lean_object* v_toBind_72_; lean_object* v_binderName_73_; lean_object* v_binderType_74_; lean_object* v_body_75_; uint8_t v_binderInfo_76_; lean_object* v___f_77_; lean_object* v_d_78_; lean_object* v___x_79_; lean_object* v___f_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v_toBind_72_ = lean_ctor_get(v_inst_67_, 1);
lean_inc(v_toBind_72_);
v_binderName_73_ = lean_ctor_get(v_a_71_, 0);
lean_inc(v_binderName_73_);
v_binderType_74_ = lean_ctor_get(v_a_71_, 1);
lean_inc_ref(v_binderType_74_);
v_body_75_ = lean_ctor_get(v_a_71_, 2);
lean_inc_ref(v_body_75_);
v_binderInfo_76_ = lean_ctor_get_uint8(v_a_71_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_71_, 3);
lean_inc(v_f_69_);
lean_inc_ref(v_inst_68_);
lean_inc_ref(v_inst_67_);
lean_inc_ref(v_fvars_70_);
v___f_77_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg___lam__0), 6, 5);
lean_closure_set(v___f_77_, 0, v_fvars_70_);
lean_closure_set(v___f_77_, 1, v_inst_67_);
lean_closure_set(v___f_77_, 2, v_inst_68_);
lean_closure_set(v___f_77_, 3, v_f_69_);
lean_closure_set(v___f_77_, 4, v_body_75_);
v_d_78_ = lean_expr_instantiate_rev(v_binderType_74_, v_fvars_70_);
lean_dec_ref(v_fvars_70_);
lean_dec_ref(v_binderType_74_);
v___x_79_ = lean_box(v_binderInfo_76_);
lean_inc_ref(v_d_78_);
v___f_80_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___redArg___lam__1___boxed), 7, 6);
lean_closure_set(v___f_80_, 0, v_inst_68_);
lean_closure_set(v___f_80_, 1, v_inst_67_);
lean_closure_set(v___f_80_, 2, v_binderName_73_);
lean_closure_set(v___f_80_, 3, v___x_79_);
lean_closure_set(v___f_80_, 4, v_d_78_);
lean_closure_set(v___f_80_, 5, v___f_77_);
v___x_81_ = lean_apply_1(v_f_69_, v_d_78_);
v___x_82_ = lean_apply_4(v_toBind_72_, lean_box(0), lean_box(0), v___x_81_, v___f_80_);
return v___x_82_;
}
else
{
lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec_ref(v_inst_68_);
lean_dec_ref(v_inst_67_);
v___x_83_ = lean_expr_instantiate_rev(v_a_71_, v_fvars_70_);
lean_dec_ref(v_fvars_70_);
lean_dec_ref(v_a_71_);
v___x_84_ = lean_apply_1(v_f_69_, v___x_83_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg___lam__0(lean_object* v_fvars_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_f_88_, lean_object* v_body_89_, lean_object* v_x_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_array_push(v_fvars_85_, v_x_90_);
v___x_92_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg(v_inst_86_, v_inst_87_, v_f_88_, v___x_91_, v_body_89_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit(lean_object* v_m_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_f_96_, lean_object* v_fvars_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg(v_inst_94_, v_inst_95_, v_f_96_, v_fvars_97_, v_a_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___redArg(lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_f_102_, lean_object* v_e_103_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_105_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___redArg(v_inst_100_, v_inst_101_, v_f_102_, v___x_104_, v_e_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall(lean_object* v_m_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_f_109_, lean_object* v_e_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Meta_visitForall___redArg(v_inst_107_, v_inst_108_, v_f_109_, v_e_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__1(lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_declName_114_, lean_object* v_d_115_, lean_object* v_v_116_, lean_object* v___f_117_, lean_object* v_____r_118_){
_start:
{
uint8_t v___x_119_; uint8_t v___x_120_; lean_object* v___x_121_; 
v___x_119_ = 0;
v___x_120_ = 0;
v___x_121_ = l_Lean_Meta_withLetDecl___redArg(v_inst_112_, v_inst_113_, v_declName_114_, v_d_115_, v_v_116_, v___f_117_, v___x_119_, v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__2(lean_object* v_f_122_, lean_object* v_v_123_, lean_object* v_toBind_124_, lean_object* v___f_125_, lean_object* v_____r_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_apply_1(v_f_122_, v_v_123_);
v___x_128_ = lean_apply_4(v_toBind_124_, lean_box(0), lean_box(0), v___x_127_, v___f_125_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg(lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_f_131_, lean_object* v_fvars_132_, lean_object* v_a_133_){
_start:
{
if (lean_obj_tag(v_a_133_) == 8)
{
lean_object* v_toBind_134_; lean_object* v_declName_135_; lean_object* v_type_136_; lean_object* v_value_137_; lean_object* v_body_138_; lean_object* v___f_139_; lean_object* v_d_140_; lean_object* v_v_141_; lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v_toBind_134_ = lean_ctor_get(v_inst_129_, 1);
lean_inc_n(v_toBind_134_, 2);
v_declName_135_ = lean_ctor_get(v_a_133_, 0);
lean_inc(v_declName_135_);
v_type_136_ = lean_ctor_get(v_a_133_, 1);
lean_inc_ref(v_type_136_);
v_value_137_ = lean_ctor_get(v_a_133_, 2);
lean_inc_ref(v_value_137_);
v_body_138_ = lean_ctor_get(v_a_133_, 3);
lean_inc_ref(v_body_138_);
lean_dec_ref_known(v_a_133_, 4);
lean_inc_n(v_f_131_, 2);
lean_inc_ref(v_inst_130_);
lean_inc_ref(v_inst_129_);
lean_inc_ref(v_fvars_132_);
v___f_139_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__0), 6, 5);
lean_closure_set(v___f_139_, 0, v_fvars_132_);
lean_closure_set(v___f_139_, 1, v_inst_129_);
lean_closure_set(v___f_139_, 2, v_inst_130_);
lean_closure_set(v___f_139_, 3, v_f_131_);
lean_closure_set(v___f_139_, 4, v_body_138_);
v_d_140_ = lean_expr_instantiate_rev(v_type_136_, v_fvars_132_);
lean_dec_ref(v_type_136_);
v_v_141_ = lean_expr_instantiate_rev(v_value_137_, v_fvars_132_);
lean_dec_ref(v_fvars_132_);
lean_dec_ref(v_value_137_);
lean_inc_ref(v_v_141_);
lean_inc_ref(v_d_140_);
v___f_142_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__1), 7, 6);
lean_closure_set(v___f_142_, 0, v_inst_130_);
lean_closure_set(v___f_142_, 1, v_inst_129_);
lean_closure_set(v___f_142_, 2, v_declName_135_);
lean_closure_set(v___f_142_, 3, v_d_140_);
lean_closure_set(v___f_142_, 4, v_v_141_);
lean_closure_set(v___f_142_, 5, v___f_139_);
v___f_143_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__2), 5, 4);
lean_closure_set(v___f_143_, 0, v_f_131_);
lean_closure_set(v___f_143_, 1, v_v_141_);
lean_closure_set(v___f_143_, 2, v_toBind_134_);
lean_closure_set(v___f_143_, 3, v___f_142_);
v___x_144_ = lean_apply_1(v_f_131_, v_d_140_);
v___x_145_ = lean_apply_4(v_toBind_134_, lean_box(0), lean_box(0), v___x_144_, v___f_143_);
return v___x_145_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; 
lean_dec_ref(v_inst_130_);
lean_dec_ref(v_inst_129_);
v___x_146_ = lean_expr_instantiate_rev(v_a_133_, v_fvars_132_);
lean_dec_ref(v_fvars_132_);
lean_dec_ref(v_a_133_);
v___x_147_ = lean_apply_1(v_f_131_, v___x_146_);
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg___lam__0(lean_object* v_fvars_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_f_151_, lean_object* v_body_152_, lean_object* v_x_153_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_array_push(v_fvars_148_, v_x_153_);
v___x_155_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg(v_inst_149_, v_inst_150_, v_f_151_, v___x_154_, v_body_152_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit(lean_object* v_m_156_, lean_object* v_inst_157_, lean_object* v_inst_158_, lean_object* v_f_159_, lean_object* v_fvars_160_, lean_object* v_a_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg(v_inst_157_, v_inst_158_, v_f_159_, v_fvars_160_, v_a_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___redArg(lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_f_165_, lean_object* v_e_166_){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_168_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___redArg(v_inst_163_, v_inst_164_, v_f_165_, v___x_167_, v_e_166_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet(lean_object* v_m_169_, lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_f_172_, lean_object* v_e_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_Meta_visitLet___redArg(v_inst_170_, v_inst_171_, v_f_172_, v_e_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__0(lean_object* v_toApplicative_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_toPure_178_; lean_object* v___x_179_; 
v_toPure_178_ = lean_ctor_get(v_toApplicative_175_, 1);
lean_inc(v_toPure_178_);
lean_dec_ref(v_toApplicative_175_);
v___x_179_ = lean_apply_2(v_toPure_178_, lean_box(0), v_a_176_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__1(lean_object* v___x_180_, lean_object* v___x_181_, lean_object* v_e_182_, lean_object* v_a_183_, lean_object* v_s_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_box(0);
v___x_186_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_180_, v___x_181_, v_s_184_, v_e_182_, v_a_183_);
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_185_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__2(lean_object* v_toApplicative_188_, lean_object* v___x_189_, lean_object* v___x_190_, lean_object* v_e_191_, lean_object* v_a_192_, lean_object* v_x_193_, lean_object* v_toBind_194_, lean_object* v_a_195_){
_start:
{
lean_object* v___f_196_; lean_object* v___f_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___f_196_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__0), 3, 2);
lean_closure_set(v___f_196_, 0, v_toApplicative_188_);
lean_closure_set(v___f_196_, 1, v_a_195_);
v___f_197_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__1), 5, 4);
lean_closure_set(v___f_197_, 0, v___x_189_);
lean_closure_set(v___f_197_, 1, v___x_190_);
lean_closure_set(v___f_197_, 2, v_e_191_);
lean_closure_set(v___f_197_, 3, v_a_195_);
lean_inc(v_a_192_);
v___x_198_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_198_, 0, lean_box(0));
lean_closure_set(v___x_198_, 1, lean_box(0));
lean_closure_set(v___x_198_, 2, lean_box(0));
lean_closure_set(v___x_198_, 3, v_a_192_);
lean_closure_set(v___x_198_, 4, v___f_197_);
v___x_199_ = lean_apply_2(v_x_193_, lean_box(0), v___x_198_);
v___x_200_ = lean_apply_4(v_toBind_194_, lean_box(0), lean_box(0), v___x_199_, v___f_196_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__2___boxed(lean_object* v_toApplicative_201_, lean_object* v___x_202_, lean_object* v___x_203_, lean_object* v_e_204_, lean_object* v_a_205_, lean_object* v_x_206_, lean_object* v_toBind_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__2(v_toApplicative_201_, v___x_202_, v___x_203_, v_e_204_, v_a_205_, v_x_206_, v_toBind_207_, v_a_208_);
lean_dec(v_a_205_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__3(lean_object* v_toApplicative_210_, lean_object* v___x_211_, lean_object* v___x_212_, lean_object* v_e_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_toPure_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_toPure_215_ = lean_ctor_get(v_toApplicative_210_, 1);
lean_inc(v_toPure_215_);
lean_dec_ref(v_toApplicative_210_);
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_211_, v___x_212_, v_a_214_, v_e_213_);
v___x_217_ = lean_apply_2(v_toPure_215_, lean_box(0), v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__3___boxed(lean_object* v_toApplicative_218_, lean_object* v___x_219_, lean_object* v___x_220_, lean_object* v_e_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__3(v_toApplicative_218_, v___x_219_, v___x_220_, v_e_221_, v_a_222_);
lean_dec_ref(v_a_222_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__6(lean_object* v_fn_224_, lean_object* v_e_225_, lean_object* v_toBind_226_, lean_object* v___f_227_, lean_object* v___f_228_, lean_object* v_toApplicative_229_, lean_object* v_a_230_){
_start:
{
if (lean_obj_tag(v_a_230_) == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec_ref(v_toApplicative_229_);
v___x_231_ = lean_apply_1(v_fn_224_, v_e_225_);
lean_inc(v_toBind_226_);
v___x_232_ = lean_apply_4(v_toBind_226_, lean_box(0), lean_box(0), v___x_231_, v___f_227_);
v___x_233_ = lean_apply_4(v_toBind_226_, lean_box(0), lean_box(0), v___x_232_, v___f_228_);
return v___x_233_;
}
else
{
lean_object* v_val_234_; lean_object* v_toPure_235_; lean_object* v___x_236_; 
lean_dec(v___f_228_);
lean_dec(v___f_227_);
lean_dec(v_toBind_226_);
lean_dec_ref(v_e_225_);
lean_dec(v_fn_224_);
v_val_234_ = lean_ctor_get(v_a_230_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v_a_230_, 1);
v_toPure_235_ = lean_ctor_get(v_toApplicative_229_, 1);
lean_inc(v_toPure_235_);
lean_dec_ref(v_toApplicative_229_);
v___x_236_ = lean_apply_2(v_toPure_235_, lean_box(0), v_val_234_);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed(lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_fn_241_, lean_object* v_x_242_, lean_object* v_x_243_, lean_object* v_e_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_239_, v_inst_240_, v_fn_241_, v_x_242_, v_x_243_, v_e_244_, v_a_245_);
lean_dec(v_a_245_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4___boxed(lean_object* v_inst_247_, lean_object* v_inst_248_, lean_object* v_fn_249_, lean_object* v_x_250_, lean_object* v_x_251_, lean_object* v_arg_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4(v_inst_247_, v_inst_248_, v_fn_249_, v_x_250_, v_x_251_, v_arg_252_, v_a_253_, v_a_254_);
lean_dec(v_a_253_);
return v_res_255_;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5(lean_object* v_toApplicative_256_, lean_object* v_e_257_, lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_fn_260_, lean_object* v_x_261_, lean_object* v_x_262_, lean_object* v___x_263_, lean_object* v___x_264_, lean_object* v_a_265_, lean_object* v_toBind_266_, uint8_t v_a_267_){
_start:
{
if (v_a_267_ == 0)
{
lean_object* v_toPure_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec(v_toBind_266_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_263_);
lean_dec(v_x_262_);
lean_dec(v_fn_260_);
lean_dec_ref(v_inst_259_);
lean_dec_ref(v_inst_258_);
lean_dec_ref(v_e_257_);
v_toPure_268_ = lean_ctor_get(v_toApplicative_256_, 1);
lean_inc(v_toPure_268_);
lean_dec_ref(v_toApplicative_256_);
v___x_269_ = lean_box(0);
v___x_270_ = lean_apply_2(v_toPure_268_, lean_box(0), v___x_269_);
return v___x_270_;
}
else
{
switch(lean_obj_tag(v_e_257_))
{
case 7:
{
lean_object* v___x_271_; lean_object* v___x_745__overap_272_; lean_object* v___x_273_; 
lean_dec(v_toBind_266_);
lean_dec_ref(v_toApplicative_256_);
v___x_271_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed), 7, 5);
lean_closure_set(v___x_271_, 0, v_inst_258_);
lean_closure_set(v___x_271_, 1, v_inst_259_);
lean_closure_set(v___x_271_, 2, v_fn_260_);
lean_closure_set(v___x_271_, 3, v_x_261_);
lean_closure_set(v___x_271_, 4, v_x_262_);
v___x_745__overap_272_ = l_Lean_Meta_visitForall___redArg(v___x_263_, v___x_264_, v___x_271_, v_e_257_);
lean_inc(v_a_265_);
v___x_273_ = lean_apply_1(v___x_745__overap_272_, v_a_265_);
return v___x_273_;
}
case 6:
{
lean_object* v___x_274_; lean_object* v___x_751__overap_275_; lean_object* v___x_276_; 
lean_dec(v_toBind_266_);
lean_dec_ref(v_toApplicative_256_);
v___x_274_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed), 7, 5);
lean_closure_set(v___x_274_, 0, v_inst_258_);
lean_closure_set(v___x_274_, 1, v_inst_259_);
lean_closure_set(v___x_274_, 2, v_fn_260_);
lean_closure_set(v___x_274_, 3, v_x_261_);
lean_closure_set(v___x_274_, 4, v_x_262_);
v___x_751__overap_275_ = l_Lean_Meta_visitLambda___redArg(v___x_263_, v___x_264_, v___x_274_, v_e_257_);
lean_inc(v_a_265_);
v___x_276_ = lean_apply_1(v___x_751__overap_275_, v_a_265_);
return v___x_276_;
}
case 8:
{
lean_object* v___x_277_; lean_object* v___x_758__overap_278_; lean_object* v___x_279_; 
lean_dec(v_toBind_266_);
lean_dec_ref(v_toApplicative_256_);
v___x_277_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___boxed), 7, 5);
lean_closure_set(v___x_277_, 0, v_inst_258_);
lean_closure_set(v___x_277_, 1, v_inst_259_);
lean_closure_set(v___x_277_, 2, v_fn_260_);
lean_closure_set(v___x_277_, 3, v_x_261_);
lean_closure_set(v___x_277_, 4, v_x_262_);
v___x_758__overap_278_ = l_Lean_Meta_visitLet___redArg(v___x_263_, v___x_264_, v___x_277_, v_e_257_);
lean_inc(v_a_265_);
v___x_279_ = lean_apply_1(v___x_758__overap_278_, v_a_265_);
return v___x_279_;
}
case 5:
{
lean_object* v_fn_280_; lean_object* v_arg_281_; lean_object* v___f_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_263_);
lean_dec_ref(v_toApplicative_256_);
v_fn_280_ = lean_ctor_get(v_e_257_, 0);
lean_inc_ref(v_fn_280_);
v_arg_281_ = lean_ctor_get(v_e_257_, 1);
lean_inc_ref(v_arg_281_);
lean_dec_ref_known(v_e_257_, 2);
lean_inc(v_a_265_);
lean_inc(v_x_262_);
lean_inc(v_fn_260_);
lean_inc_ref(v_inst_259_);
lean_inc_ref(v_inst_258_);
v___f_282_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_282_, 0, v_inst_258_);
lean_closure_set(v___f_282_, 1, v_inst_259_);
lean_closure_set(v___f_282_, 2, v_fn_260_);
lean_closure_set(v___f_282_, 3, v_x_261_);
lean_closure_set(v___f_282_, 4, v_x_262_);
lean_closure_set(v___f_282_, 5, v_arg_281_);
lean_closure_set(v___f_282_, 6, v_a_265_);
v___x_283_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_258_, v_inst_259_, v_fn_260_, v_x_261_, v_x_262_, v_fn_280_, v_a_265_);
v___x_284_ = lean_apply_4(v_toBind_266_, lean_box(0), lean_box(0), v___x_283_, v___f_282_);
return v___x_284_;
}
case 10:
{
lean_object* v_expr_285_; lean_object* v___x_286_; 
lean_dec(v_toBind_266_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_263_);
lean_dec_ref(v_toApplicative_256_);
v_expr_285_ = lean_ctor_get(v_e_257_, 1);
lean_inc_ref(v_expr_285_);
lean_dec_ref_known(v_e_257_, 2);
v___x_286_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_258_, v_inst_259_, v_fn_260_, v_x_261_, v_x_262_, v_expr_285_, v_a_265_);
return v___x_286_;
}
case 11:
{
lean_object* v_struct_287_; lean_object* v___x_288_; 
lean_dec(v_toBind_266_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_263_);
lean_dec_ref(v_toApplicative_256_);
v_struct_287_ = lean_ctor_get(v_e_257_, 2);
lean_inc_ref(v_struct_287_);
lean_dec_ref_known(v_e_257_, 3);
v___x_288_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_258_, v_inst_259_, v_fn_260_, v_x_261_, v_x_262_, v_struct_287_, v_a_265_);
return v___x_288_;
}
default: 
{
lean_object* v_toPure_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
lean_dec(v_toBind_266_);
lean_dec_ref(v___x_264_);
lean_dec_ref(v___x_263_);
lean_dec(v_x_262_);
lean_dec(v_fn_260_);
lean_dec_ref(v_inst_259_);
lean_dec_ref(v_inst_258_);
lean_dec_ref(v_e_257_);
v_toPure_289_ = lean_ctor_get(v_toApplicative_256_, 1);
lean_inc(v_toPure_289_);
lean_dec_ref(v_toApplicative_256_);
v___x_290_ = lean_box(0);
v___x_291_ = lean_apply_2(v_toPure_289_, lean_box(0), v___x_290_);
return v___x_291_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_toApplicative_256_ = stack[0].m_obj;
lean_object* v_e_257_ = stack[1].m_obj;
lean_object* v_inst_258_ = stack[2].m_obj;
lean_object* v_inst_259_ = stack[3].m_obj;
lean_object* v_fn_260_ = stack[4].m_obj;
lean_object* v_x_261_ = stack[5].m_obj;
lean_object* v_x_262_ = stack[6].m_obj;
lean_object* v___x_263_ = stack[7].m_obj;
lean_object* v___x_264_ = stack[8].m_obj;
lean_object* v_a_265_ = stack[9].m_obj;
lean_object* v_toBind_266_ = stack[10].m_obj;
uint8_t v_a_267_ = stack[11].m_num;
lean_object* v_res_292_;
v_res_292_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5(v_toApplicative_256_, v_e_257_, v_inst_258_, v_inst_259_, v_fn_260_, v_x_261_, v_x_262_, v___x_263_, v___x_264_, v_a_265_, v_toBind_266_, v_a_267_);
stack->m_obj
 = v_res_292_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___boxed(lean_object* v_toApplicative_293_, lean_object* v_e_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_fn_297_, lean_object* v_x_298_, lean_object* v_x_299_, lean_object* v___x_300_, lean_object* v___x_301_, lean_object* v_a_302_, lean_object* v_toBind_303_, lean_object* v_a_304_){
_start:
{
uint8_t v_a_boxed_305_; lean_object* v_res_306_; 
v_a_boxed_305_ = lean_unbox(v_a_304_);
v_res_306_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5(v_toApplicative_293_, v_e_294_, v_inst_295_, v_inst_296_, v_fn_297_, v_x_298_, v_x_299_, v___x_300_, v___x_301_, v_a_302_, v_toBind_303_, v_a_boxed_305_);
lean_dec(v_a_302_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_fn_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_e_312_, lean_object* v_a_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___f_318_; lean_object* v___f_319_; lean_object* v___x_320_; lean_object* v_toApplicative_321_; lean_object* v_toBind_322_; lean_object* v___f_323_; lean_object* v___f_324_; lean_object* v___f_325_; lean_object* v___f_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_314_ = ((lean_object*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__0));
v___x_315_ = ((lean_object*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___closed__1));
lean_inc_ref(v_inst_307_);
v___x_316_ = l_Lean_MonadCacheT_instMonad___redArg(v_x_310_, v___x_314_, v___x_315_, v_inst_307_);
v___x_317_ = l_Lean_MonadCacheT_instMonadControl___redArg(v_x_310_, v___x_314_, v___x_315_);
lean_inc_ref_n(v_inst_308_, 2);
lean_inc_ref(v___x_317_);
v___f_318_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_318_, 0, v___x_317_);
lean_closure_set(v___f_318_, 1, v_inst_308_);
v___f_319_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_319_, 0, v___x_317_);
lean_closure_set(v___f_319_, 1, v_inst_308_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___f_318_);
lean_ctor_set(v___x_320_, 1, v___f_319_);
v_toApplicative_321_ = lean_ctor_get(v_inst_307_, 0);
lean_inc_ref_n(v_toApplicative_321_, 4);
v_toBind_322_ = lean_ctor_get(v_inst_307_, 1);
lean_inc_n(v_toBind_322_, 5);
lean_inc_n(v_x_311_, 2);
lean_inc_n(v_a_313_, 3);
lean_inc_ref_n(v_e_312_, 3);
v___f_323_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_323_, 0, v_toApplicative_321_);
lean_closure_set(v___f_323_, 1, v___x_314_);
lean_closure_set(v___f_323_, 2, v___x_315_);
lean_closure_set(v___f_323_, 3, v_e_312_);
lean_closure_set(v___f_323_, 4, v_a_313_);
lean_closure_set(v___f_323_, 5, v_x_311_);
lean_closure_set(v___f_323_, 6, v_toBind_322_);
v___f_324_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__3___boxed), 5, 4);
lean_closure_set(v___f_324_, 0, v_toApplicative_321_);
lean_closure_set(v___f_324_, 1, v___x_314_);
lean_closure_set(v___f_324_, 2, v___x_315_);
lean_closure_set(v___f_324_, 3, v_e_312_);
lean_inc(v_fn_309_);
v___f_325_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___boxed), 12, 11);
lean_closure_set(v___f_325_, 0, v_toApplicative_321_);
lean_closure_set(v___f_325_, 1, v_e_312_);
lean_closure_set(v___f_325_, 2, v_inst_307_);
lean_closure_set(v___f_325_, 3, v_inst_308_);
lean_closure_set(v___f_325_, 4, v_fn_309_);
lean_closure_set(v___f_325_, 5, v_x_310_);
lean_closure_set(v___f_325_, 6, v_x_311_);
lean_closure_set(v___f_325_, 7, v___x_316_);
lean_closure_set(v___f_325_, 8, v___x_320_);
lean_closure_set(v___f_325_, 9, v_a_313_);
lean_closure_set(v___f_325_, 10, v_toBind_322_);
v___f_326_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__6), 7, 6);
lean_closure_set(v___f_326_, 0, v_fn_309_);
lean_closure_set(v___f_326_, 1, v_e_312_);
lean_closure_set(v___f_326_, 2, v_toBind_322_);
lean_closure_set(v___f_326_, 3, v___f_325_);
lean_closure_set(v___f_326_, 4, v___f_323_);
lean_closure_set(v___f_326_, 5, v_toApplicative_321_);
v___x_327_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_327_, 0, lean_box(0));
lean_closure_set(v___x_327_, 1, lean_box(0));
lean_closure_set(v___x_327_, 2, v_a_313_);
v___x_328_ = lean_apply_2(v_x_311_, lean_box(0), v___x_327_);
v___x_329_ = lean_apply_4(v_toBind_322_, lean_box(0), lean_box(0), v___x_328_, v___f_324_);
v___x_330_ = lean_apply_4(v_toBind_322_, lean_box(0), lean_box(0), v___x_329_, v___f_326_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg___lam__4(lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_fn_333_, lean_object* v_x_334_, lean_object* v_x_335_, lean_object* v_arg_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_331_, v_inst_332_, v_fn_333_, v_x_334_, v_x_335_, v_arg_336_, v_a_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit(lean_object* v_m_340_, lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_fn_343_, lean_object* v_x_344_, lean_object* v_x_345_, lean_object* v_e_346_, lean_object* v_a_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_341_, v_inst_342_, v_fn_343_, v_x_344_, v_x_345_, v_e_346_, v_a_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___boxed(lean_object* v_m_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_fn_352_, lean_object* v_x_353_, lean_object* v_x_354_, lean_object* v_e_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit(v_m_349_, v_inst_350_, v_inst_351_, v_fn_352_, v_x_353_, v_x_354_, v_e_355_, v_a_356_);
lean_dec(v_a_356_);
return v_res_357_;
}
}
lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__0(lean_object* v_x_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_apply_1(v_x_358_, lean_box(0));
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT void l_Lean_Meta_forEachExpr_x27___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_358_ = stack[0].m_obj;
lean_object* v___y_359_ = stack[1].m_obj;
lean_object* v___y_360_ = stack[2].m_obj;
lean_object* v___y_361_ = stack[3].m_obj;
lean_object* v___y_362_ = stack[4].m_obj;
lean_object* v_res_366_;
v_res_366_ = l_Lean_Meta_forEachExpr_x27___redArg___lam__0(v_x_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
stack->m_obj
 = v_res_366_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__0___boxed(lean_object* v_x_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Meta_forEachExpr_x27___redArg___lam__0(v_x_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__1(lean_object* v_inst_374_, lean_object* v_00_u03b1_375_, lean_object* v_x_376_){
_start:
{
lean_object* v___f_377_; lean_object* v___x_378_; 
v___f_377_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_377_, 0, v_x_376_);
v___x_378_ = lean_apply_2(v_inst_374_, lean_box(0), v___f_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__2(lean_object* v_toPure_379_, lean_object* v_____x_380_){
_start:
{
lean_object* v_fst_381_; lean_object* v___x_382_; 
v_fst_381_ = lean_ctor_get(v_____x_380_, 0);
lean_inc(v_fst_381_);
lean_dec_ref(v_____x_380_);
v___x_382_ = lean_apply_2(v_toPure_379_, lean_box(0), v_fst_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__3(lean_object* v_a_383_, lean_object* v_toPure_384_, lean_object* v_s_385_){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v_a_383_);
lean_ctor_set(v___x_386_, 1, v_s_385_);
v___x_387_ = lean_apply_2(v_toPure_384_, lean_box(0), v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__4(lean_object* v_toPure_388_, lean_object* v_ref_389_, lean_object* v_x_390_, lean_object* v_toBind_391_, lean_object* v_a_392_){
_start:
{
lean_object* v___f_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___f_393_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__3), 3, 2);
lean_closure_set(v___f_393_, 0, v_a_392_);
lean_closure_set(v___f_393_, 1, v_toPure_388_);
v___x_394_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_394_, 0, lean_box(0));
lean_closure_set(v___x_394_, 1, lean_box(0));
lean_closure_set(v___x_394_, 2, v_ref_389_);
v___x_395_ = lean_apply_2(v_x_390_, lean_box(0), v___x_394_);
v___x_396_ = lean_apply_4(v_toBind_391_, lean_box(0), lean_box(0), v___x_395_, v___f_393_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__5(lean_object* v_toPure_397_, lean_object* v_x_398_, lean_object* v_toBind_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_fn_402_, lean_object* v_x_403_, lean_object* v_input_404_, lean_object* v_ref_405_){
_start:
{
lean_object* v___f_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
lean_inc(v_toBind_399_);
lean_inc(v_x_398_);
lean_inc(v_ref_405_);
v___f_406_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__4), 5, 4);
lean_closure_set(v___f_406_, 0, v_toPure_397_);
lean_closure_set(v___f_406_, 1, v_ref_405_);
lean_closure_set(v___f_406_, 2, v_x_398_);
lean_closure_set(v___f_406_, 3, v_toBind_399_);
v___x_407_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___redArg(v_inst_400_, v_inst_401_, v_fn_402_, v_x_403_, v_x_398_, v_input_404_, v_ref_405_);
lean_dec(v_ref_405_);
v___x_408_ = lean_apply_4(v_toBind_399_, lean_box(0), lean_box(0), v___x_407_, v___f_406_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = lean_box(0);
v___x_410_ = lean_unsigned_to_nat(16u);
v___x_411_ = lean_mk_array(v___x_410_, v___x_409_);
return v___x_411_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__1(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_412_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___redArg___closed__0, &l_Lean_Meta_forEachExpr_x27___redArg___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__0);
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v___x_412_);
return v___x_414_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__2(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___redArg___closed__1, &l_Lean_Meta_forEachExpr_x27___redArg___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__1);
v___x_416_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_416_, 0, lean_box(0));
lean_closure_set(v___x_416_, 1, lean_box(0));
lean_closure_set(v___x_416_, 2, v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg(lean_object* v_inst_417_, lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_input_420_, lean_object* v_fn_421_){
_start:
{
lean_object* v_x_422_; lean_object* v_toApplicative_423_; lean_object* v_toBind_424_; lean_object* v_toPure_425_; lean_object* v_x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___f_429_; lean_object* v___f_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_x_422_ = lean_box(0);
v_toApplicative_423_ = lean_ctor_get(v_inst_417_, 0);
v_toBind_424_ = lean_ctor_get(v_inst_417_, 1);
lean_inc_n(v_toBind_424_, 3);
v_toPure_425_ = lean_ctor_get(v_toApplicative_423_, 1);
lean_inc_n(v_toPure_425_, 2);
lean_inc(v_inst_418_);
v_x_426_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__1), 3, 1);
lean_closure_set(v_x_426_, 0, v_inst_418_);
v___x_427_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___redArg___closed__2, &l_Lean_Meta_forEachExpr_x27___redArg___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__2);
v___x_428_ = l_Lean_Meta_forEachExpr_x27___redArg___lam__1(v_inst_418_, lean_box(0), v___x_427_);
v___f_429_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__2), 2, 1);
lean_closure_set(v___f_429_, 0, v_toPure_425_);
v___f_430_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__5), 9, 8);
lean_closure_set(v___f_430_, 0, v_toPure_425_);
lean_closure_set(v___f_430_, 1, v_x_426_);
lean_closure_set(v___f_430_, 2, v_toBind_424_);
lean_closure_set(v___f_430_, 3, v_inst_417_);
lean_closure_set(v___f_430_, 4, v_inst_419_);
lean_closure_set(v___f_430_, 5, v_fn_421_);
lean_closure_set(v___f_430_, 6, v_x_422_);
lean_closure_set(v___f_430_, 7, v_input_420_);
v___x_431_ = lean_apply_4(v_toBind_424_, lean_box(0), lean_box(0), v___x_428_, v___f_430_);
v___x_432_ = lean_apply_4(v_toBind_424_, lean_box(0), lean_box(0), v___x_431_, v___f_429_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27(lean_object* v_m_433_, lean_object* v_inst_434_, lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_input_437_, lean_object* v_fn_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Meta_forEachExpr_x27___redArg(v_inst_434_, v_inst_435_, v_inst_436_, v_input_437_, v_fn_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg___lam__0(lean_object* v_toPure_440_, lean_object* v_____r_441_){
_start:
{
uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_442_ = 1;
v___x_443_ = lean_box(v___x_442_);
v___x_444_ = lean_apply_2(v_toPure_440_, lean_box(0), v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg___lam__1(lean_object* v_f_445_, lean_object* v_toBind_446_, lean_object* v___f_447_, lean_object* v_e_448_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_apply_1(v_f_445_, v_e_448_);
v___x_450_ = lean_apply_4(v_toBind_446_, lean_box(0), lean_box(0), v___x_449_, v___f_447_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg(lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_e_454_, lean_object* v_f_455_){
_start:
{
lean_object* v_toApplicative_456_; lean_object* v_toBind_457_; lean_object* v_toPure_458_; lean_object* v___f_459_; lean_object* v___f_460_; lean_object* v___x_461_; 
v_toApplicative_456_ = lean_ctor_get(v_inst_451_, 0);
v_toBind_457_ = lean_ctor_get(v_inst_451_, 1);
v_toPure_458_ = lean_ctor_get(v_toApplicative_456_, 1);
lean_inc(v_toPure_458_);
v___f_459_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___redArg___lam__0), 2, 1);
lean_closure_set(v___f_459_, 0, v_toPure_458_);
lean_inc(v_toBind_457_);
v___f_460_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___redArg___lam__1), 4, 3);
lean_closure_set(v___f_460_, 0, v_f_455_);
lean_closure_set(v___f_460_, 1, v_toBind_457_);
lean_closure_set(v___f_460_, 2, v___f_459_);
v___x_461_ = l_Lean_Meta_forEachExpr_x27___redArg(v_inst_451_, v_inst_452_, v_inst_453_, v_e_454_, v___f_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr(lean_object* v_m_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_e_466_, lean_object* v_f_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Meta_forEachExpr___redArg(v_inst_463_, v_inst_464_, v_inst_465_, v_e_466_, v_f_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0(lean_object* v_toPure_469_, lean_object* v_____do__lift_470_){
_start:
{
lean_object* v_userName_471_; uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_userName_471_ = lean_ctor_get(v_____do__lift_470_, 0);
v___x_472_ = l_Lean_Name_isAnonymous(v_userName_471_);
v___x_473_ = lean_box(v___x_472_);
v___x_474_ = lean_apply_2(v_toPure_469_, lean_box(0), v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0___boxed(lean_object* v_toPure_475_, lean_object* v_____do__lift_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0(v_toPure_475_, v_____do__lift_476_);
lean_dec_ref(v_____do__lift_476_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg(lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_x_480_){
_start:
{
lean_object* v_toApplicative_481_; 
v_toApplicative_481_ = lean_ctor_get(v_inst_478_, 0);
lean_inc_ref(v_toApplicative_481_);
if (lean_obj_tag(v_x_480_) == 2)
{
lean_object* v_toBind_482_; lean_object* v_toPure_483_; lean_object* v_mvarId_484_; lean_object* v___f_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_toBind_482_ = lean_ctor_get(v_inst_478_, 1);
lean_inc(v_toBind_482_);
lean_dec_ref(v_inst_478_);
v_toPure_483_ = lean_ctor_get(v_toApplicative_481_, 1);
lean_inc(v_toPure_483_);
lean_dec_ref(v_toApplicative_481_);
v_mvarId_484_ = lean_ctor_get(v_x_480_, 0);
lean_inc(v_mvarId_484_);
lean_dec_ref_known(v_x_480_, 1);
v___f_485_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_485_, 0, v_toPure_483_);
v___x_486_ = lean_alloc_closure((void*)(l_Lean_MVarId_getDecl___boxed), 6, 1);
lean_closure_set(v___x_486_, 0, v_mvarId_484_);
v___x_487_ = lean_apply_2(v_inst_479_, lean_box(0), v___x_486_);
v___x_488_ = lean_apply_4(v_toBind_482_, lean_box(0), lean_box(0), v___x_487_, v___f_485_);
return v___x_488_;
}
else
{
lean_object* v_toPure_489_; uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec_ref(v_x_480_);
lean_dec(v_inst_479_);
lean_dec_ref(v_inst_478_);
v_toPure_489_ = lean_ctor_get(v_toApplicative_481_, 1);
lean_inc(v_toPure_489_);
lean_dec_ref(v_toApplicative_481_);
v___x_490_ = 0;
v___x_491_ = lean_box(v___x_490_);
v___x_492_ = lean_apply_2(v_toPure_489_, lean_box(0), v___x_491_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName(lean_object* v_m_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_x_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg(v_inst_494_, v_inst_495_, v_x_496_);
return v___x_497_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0(lean_object* v_k_498_, lean_object* v_b_499_, lean_object* v_c_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; 
lean_inc(v___y_504_);
lean_inc_ref(v___y_503_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
v___x_506_ = lean_apply_7(v_k_498_, v_b_499_, v_c_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, lean_box(0));
return v___x_506_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_498_ = stack[0].m_obj;
lean_object* v_b_499_ = stack[1].m_obj;
lean_object* v_c_500_ = stack[2].m_obj;
lean_object* v___y_501_ = stack[3].m_obj;
lean_object* v___y_502_ = stack[4].m_obj;
lean_object* v___y_503_ = stack[5].m_obj;
lean_object* v___y_504_ = stack[6].m_obj;
lean_object* v_res_507_;
v_res_507_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0(v_k_498_, v_b_499_, v_c_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
stack->m_obj
 = v_res_507_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0___boxed(lean_object* v_k_508_, lean_object* v_b_509_, lean_object* v_c_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0(v_k_508_, v_b_509_, v_c_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
return v_res_516_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(lean_object* v_type_517_, lean_object* v_maxFVars_x3f_518_, lean_object* v_k_519_, uint8_t v_cleanupAnnotations_520_, uint8_t v_whnfType_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v___f_527_; lean_object* v___x_528_; 
v___f_527_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_527_, 0, v_k_519_);
v___x_528_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_517_, v_maxFVars_x3f_518_, v___f_527_, v_cleanupAnnotations_520_, v_whnfType_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_528_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
v_a_537_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_528_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_528_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_517_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_518_ = stack[1].m_obj;
lean_object* v_k_519_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_520_ = stack[3].m_num;
uint8_t v_whnfType_521_ = stack[4].m_num;
lean_object* v___y_522_ = stack[5].m_obj;
lean_object* v___y_523_ = stack[6].m_obj;
lean_object* v___y_524_ = stack[7].m_obj;
lean_object* v___y_525_ = stack[8].m_obj;
lean_object* v_res_545_;
v_res_545_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(v_type_517_, v_maxFVars_x3f_518_, v_k_519_, v_cleanupAnnotations_520_, v_whnfType_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
stack->m_obj
 = v_res_545_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg___boxed(lean_object* v_type_546_, lean_object* v_maxFVars_x3f_547_, lean_object* v_k_548_, lean_object* v_cleanupAnnotations_549_, lean_object* v_whnfType_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_556_; uint8_t v_whnfType_boxed_557_; lean_object* v_res_558_; 
v_cleanupAnnotations_boxed_556_ = lean_unbox(v_cleanupAnnotations_549_);
v_whnfType_boxed_557_ = lean_unbox(v_whnfType_550_);
v_res_558_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(v_type_546_, v_maxFVars_x3f_547_, v_k_548_, v_cleanupAnnotations_boxed_556_, v_whnfType_boxed_557_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
return v_res_558_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0(lean_object* v_00_u03b1_559_, lean_object* v_type_560_, lean_object* v_maxFVars_x3f_561_, lean_object* v_k_562_, uint8_t v_cleanupAnnotations_563_, uint8_t v_whnfType_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(v_type_560_, v_maxFVars_x3f_561_, v_k_562_, v_cleanupAnnotations_563_, v_whnfType_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
return v___x_570_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_560_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_561_ = stack[2].m_obj;
lean_object* v_k_562_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_563_ = stack[4].m_num;
uint8_t v_whnfType_564_ = stack[5].m_num;
lean_object* v___y_565_ = stack[6].m_obj;
lean_object* v___y_566_ = stack[7].m_obj;
lean_object* v___y_567_ = stack[8].m_obj;
lean_object* v___y_568_ = stack[9].m_obj;
lean_object* v_res_571_;
v_res_571_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0(lean_box(0), v_type_560_, v_maxFVars_x3f_561_, v_k_562_, v_cleanupAnnotations_563_, v_whnfType_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
stack->m_obj
 = v_res_571_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___boxed(lean_object* v_00_u03b1_572_, lean_object* v_type_573_, lean_object* v_maxFVars_x3f_574_, lean_object* v_k_575_, lean_object* v_cleanupAnnotations_576_, lean_object* v_whnfType_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_583_; uint8_t v_whnfType_boxed_584_; lean_object* v_res_585_; 
v_cleanupAnnotations_boxed_583_ = lean_unbox(v_cleanupAnnotations_576_);
v_whnfType_boxed_584_ = lean_unbox(v_whnfType_577_);
v_res_585_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0(v_00_u03b1_572_, v_type_573_, v_maxFVars_x3f_574_, v_k_575_, v_cleanupAnnotations_boxed_583_, v_whnfType_boxed_584_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
return v_res_585_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(lean_object* v_e_586_, lean_object* v___y_587_){
_start:
{
uint8_t v___x_589_; 
v___x_589_ = l_Lean_Expr_hasMVar(v_e_586_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v_e_586_);
return v___x_590_;
}
else
{
lean_object* v___x_591_; lean_object* v_mctx_592_; lean_object* v___x_593_; lean_object* v_fst_594_; lean_object* v_snd_595_; lean_object* v___x_596_; lean_object* v_cache_597_; lean_object* v_zetaDeltaFVarIds_598_; lean_object* v_postponed_599_; lean_object* v_diag_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_609_; 
v___x_591_ = lean_st_ref_get(v___y_587_);
v_mctx_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc_ref(v_mctx_592_);
lean_dec(v___x_591_);
v___x_593_ = l_Lean_instantiateMVarsCore(v_mctx_592_, v_e_586_);
v_fst_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_fst_594_);
v_snd_595_ = lean_ctor_get(v___x_593_, 1);
lean_inc(v_snd_595_);
lean_dec_ref(v___x_593_);
v___x_596_ = lean_st_ref_take(v___y_587_);
v_cache_597_ = lean_ctor_get(v___x_596_, 1);
v_zetaDeltaFVarIds_598_ = lean_ctor_get(v___x_596_, 2);
v_postponed_599_ = lean_ctor_get(v___x_596_, 3);
v_diag_600_ = lean_ctor_get(v___x_596_, 4);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; 
v_unused_610_ = lean_ctor_get(v___x_596_, 0);
lean_dec(v_unused_610_);
v___x_602_ = v___x_596_;
v_isShared_603_ = v_isSharedCheck_609_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_diag_600_);
lean_inc(v_postponed_599_);
lean_inc(v_zetaDeltaFVarIds_598_);
lean_inc(v_cache_597_);
lean_dec(v___x_596_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_609_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v_snd_595_);
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_snd_595_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_cache_597_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_zetaDeltaFVarIds_598_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v_postponed_599_);
lean_ctor_set(v_reuseFailAlloc_608_, 4, v_diag_600_);
v___x_605_ = v_reuseFailAlloc_608_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_st_ref_put(v___y_587_, v___x_605_);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v_fst_594_);
return v___x_607_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_586_ = stack[0].m_obj;
lean_object* v___y_587_ = stack[1].m_obj;
lean_object* v_res_611_;
v_res_611_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(v_e_586_, v___y_587_);
stack->m_obj
 = v_res_611_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg___boxed(lean_object* v_e_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(v_e_612_, v___y_613_);
lean_dec(v___y_613_);
return v_res_615_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3(lean_object* v_e_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(v_e_616_, v___y_618_);
return v___x_622_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_616_ = stack[0].m_obj;
lean_object* v___y_617_ = stack[1].m_obj;
lean_object* v___y_618_ = stack[2].m_obj;
lean_object* v___y_619_ = stack[3].m_obj;
lean_object* v___y_620_ = stack[4].m_obj;
lean_object* v_res_623_;
v_res_623_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3(v_e_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
stack->m_obj
 = v_res_623_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___boxed(lean_object* v_e_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3(v_e_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
return v_res_630_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0(lean_object* v_a_631_, lean_object* v___x_632_, lean_object* v___x_633_, lean_object* v_val_634_, lean_object* v___x_635_, lean_object* v_xs_636_, lean_object* v_x_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = lean_array_get_size(v_xs_636_);
v___x_644_ = lean_nat_dec_lt(v_a_631_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
lean_dec(v___x_635_);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_632_);
return v___x_645_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_array_get_borrowed(v___x_633_, v_xs_636_, v_a_631_);
v___x_647_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_646_, v___y_638_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_647_, 1);
v___x_649_ = l_Lean_LocalDecl_userName(v_a_648_);
lean_dec(v_a_648_);
v___x_650_ = l_Lean_Core_mkFreshUserName(v___x_649_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_676_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_676_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_676_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_676_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v_mctx_659_; lean_object* v_cache_660_; lean_object* v_zetaDeltaFVarIds_661_; lean_object* v_postponed_662_; lean_object* v_diag_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_675_; 
v___x_655_ = lean_st_ref_take(v_val_634_);
lean_inc(v___x_635_);
v___x_656_ = lean_array_push(v___x_655_, v___x_635_);
v___x_657_ = lean_st_ref_put(v_val_634_, v___x_656_);
v___x_658_ = lean_st_ref_take(v___y_639_);
v_mctx_659_ = lean_ctor_get(v___x_658_, 0);
v_cache_660_ = lean_ctor_get(v___x_658_, 1);
v_zetaDeltaFVarIds_661_ = lean_ctor_get(v___x_658_, 2);
v_postponed_662_ = lean_ctor_get(v___x_658_, 3);
v_diag_663_ = lean_ctor_get(v___x_658_, 4);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_675_ == 0)
{
v___x_665_ = v___x_658_;
v_isShared_666_ = v_isSharedCheck_675_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_diag_663_);
lean_inc(v_postponed_662_);
lean_inc(v_zetaDeltaFVarIds_661_);
lean_inc(v_cache_660_);
lean_inc(v_mctx_659_);
lean_dec(v___x_658_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_675_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = l_Lean_MetavarContext_setMVarUserNameTemporarily(v_mctx_659_, v___x_635_, v_a_651_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_667_);
v___x_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_cache_660_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_zetaDeltaFVarIds_661_);
lean_ctor_set(v_reuseFailAlloc_674_, 3, v_postponed_662_);
lean_ctor_set(v_reuseFailAlloc_674_, 4, v_diag_663_);
v___x_669_ = v_reuseFailAlloc_674_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_670_ = lean_st_ref_put(v___y_639_, v___x_669_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v___x_632_);
v___x_672_ = v___x_653_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_632_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec(v___x_635_);
v_a_677_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_650_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_650_);
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
else
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
lean_dec(v___x_635_);
v_a_685_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_647_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_647_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_631_ = stack[0].m_obj;
lean_object* v___x_632_ = stack[1].m_obj;
lean_object* v___x_633_ = stack[2].m_obj;
lean_object* v_val_634_ = stack[3].m_obj;
lean_object* v___x_635_ = stack[4].m_obj;
lean_object* v_xs_636_ = stack[5].m_obj;
lean_object* v_x_637_ = stack[6].m_obj;
lean_object* v___y_638_ = stack[7].m_obj;
lean_object* v___y_639_ = stack[8].m_obj;
lean_object* v___y_640_ = stack[9].m_obj;
lean_object* v___y_641_ = stack[10].m_obj;
lean_object* v_res_693_;
v_res_693_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0(v_a_631_, v___x_632_, v___x_633_, v_val_634_, v___x_635_, v_xs_636_, v_x_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
stack->m_obj
 = v_res_693_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0___boxed(lean_object* v_a_694_, lean_object* v___x_695_, lean_object* v___x_696_, lean_object* v_val_697_, lean_object* v___x_698_, lean_object* v_xs_699_, lean_object* v_x_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0(v_a_694_, v___x_695_, v___x_696_, v_val_697_, v___x_698_, v_xs_699_, v_x_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec_ref(v_x_700_);
lean_dec_ref(v_xs_699_);
lean_dec(v_val_697_);
lean_dec_ref(v___x_696_);
lean_dec(v_a_694_);
return v_res_706_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(lean_object* v_a_707_, lean_object* v_as_708_, size_t v_i_709_, size_t v_stop_710_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_707_ = stack[0].m_obj;
lean_object* v_as_708_ = stack[1].m_obj;
size_t v_i_709_ = stack[2].m_num;
size_t v_stop_710_ = stack[3].m_num;
uint8_t v_res_718_;
v_res_718_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(v_a_707_, v_as_708_, v_i_709_, v_stop_710_);
stack->m_num = v_res_718_;
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
uint8_t l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(lean_object* v_as_727_, lean_object* v_a_728_){
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
LEAN_EXPORT void l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_727_ = stack[0].m_obj;
lean_object* v_a_728_ = stack[1].m_obj;
uint8_t v_res_735_;
v_res_735_ = l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(v_as_727_, v_a_728_);
stack->m_num = v_res_735_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1___boxed(lean_object* v_as_736_, lean_object* v_a_737_){
_start:
{
uint8_t v_res_738_; lean_object* v_r_739_; 
v_res_738_ = l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(v_as_736_, v_a_737_);
lean_dec_ref(v_a_737_);
lean_dec_ref(v_as_736_);
v_r_739_ = lean_box(v_res_738_);
return v_r_739_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(lean_object* v_upperBound_740_, lean_object* v___x_741_, lean_object* v_val_742_, lean_object* v_e_743_, lean_object* v_isTarget_744_, lean_object* v_a_745_, lean_object* v_b_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_a_753_; uint8_t v___x_757_; 
v___x_757_ = lean_nat_dec_lt(v_a_745_, v_upperBound_740_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; 
lean_dec(v_a_745_);
lean_dec(v_val_742_);
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v_b_746_);
return v___x_758_;
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___y_763_; uint8_t v___x_794_; 
v___x_759_ = lean_box(0);
v___x_760_ = l_Lean_instInhabitedExpr;
v___x_761_ = lean_array_fget_borrowed(v___x_741_, v_a_745_);
v___x_794_ = l_Lean_Expr_isMVar(v___x_761_);
if (v___x_794_ == 0)
{
v___y_763_ = v___x_794_;
goto v___jp_762_;
}
else
{
uint8_t v___x_795_; 
v___x_795_ = l_Array_contains___at___00Lean_Meta_setMVarUserNamesAt_spec__1(v_isTarget_744_, v___x_761_);
v___y_763_ = v___x_795_;
goto v___jp_762_;
}
v___jp_762_:
{
if (v___y_763_ == 0)
{
v_a_753_ = v___x_759_;
goto v___jp_752_;
}
else
{
lean_object* v___x_764_; lean_object* v___f_765_; lean_object* v___x_766_; 
v___x_764_ = l_Lean_Expr_mvarId_x21(v___x_761_);
lean_inc(v___x_764_);
lean_inc(v_val_742_);
lean_inc(v_a_745_);
v___f_765_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___lam__0___boxed), 12, 5);
lean_closure_set(v___f_765_, 0, v_a_745_);
lean_closure_set(v___f_765_, 1, v___x_759_);
lean_closure_set(v___f_765_, 2, v___x_760_);
lean_closure_set(v___f_765_, 3, v_val_742_);
lean_closure_set(v___f_765_, 4, v___x_764_);
v___x_766_ = l_Lean_MVarId_getDecl(v___x_764_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v_userName_768_; uint8_t v___x_769_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_766_, 1);
v_userName_768_ = lean_ctor_get(v_a_767_, 0);
lean_inc(v_userName_768_);
lean_dec(v_a_767_);
v___x_769_ = l_Lean_Name_isAnonymous(v_userName_768_);
lean_dec(v_userName_768_);
if (v___x_769_ == 0)
{
lean_dec_ref(v___f_765_);
v_a_753_ = v___x_759_;
goto v___jp_752_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = l_Lean_Expr_getAppFn(v_e_743_);
lean_inc(v___y_750_);
lean_inc_ref(v___y_749_);
lean_inc(v___y_748_);
lean_inc_ref(v___y_747_);
v___x_771_ = lean_infer_type(v___x_770_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; lean_object* v___x_777_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
lean_dec_ref_known(v___x_771_, 1);
v___x_773_ = lean_unsigned_to_nat(1u);
v___x_774_ = lean_nat_add(v_a_745_, v___x_773_);
v___x_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
v___x_776_ = 0;
v___x_777_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_setMVarUserNamesAt_spec__0___redArg(v_a_772_, v___x_775_, v___f_765_, v___x_776_, v___x_776_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_dec_ref_known(v___x_777_, 1);
v_a_753_ = v___x_759_;
goto v___jp_752_;
}
else
{
lean_dec(v_a_745_);
lean_dec(v_val_742_);
return v___x_777_;
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec_ref(v___f_765_);
lean_dec(v_a_745_);
lean_dec(v_val_742_);
v_a_778_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_771_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_771_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec_ref(v___f_765_);
lean_dec(v_a_745_);
lean_dec(v_val_742_);
v_a_786_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_766_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_766_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
}
v___jp_752_:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_unsigned_to_nat(1u);
v___x_755_ = lean_nat_add(v_a_745_, v___x_754_);
lean_dec(v_a_745_);
v_a_745_ = v___x_755_;
v_b_746_ = v_a_753_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_740_ = stack[0].m_obj;
lean_object* v___x_741_ = stack[1].m_obj;
lean_object* v_val_742_ = stack[2].m_obj;
lean_object* v_e_743_ = stack[3].m_obj;
lean_object* v_isTarget_744_ = stack[4].m_obj;
lean_object* v_a_745_ = stack[5].m_obj;
lean_object* v_b_746_ = stack[6].m_obj;
lean_object* v___y_747_ = stack[7].m_obj;
lean_object* v___y_748_ = stack[8].m_obj;
lean_object* v___y_749_ = stack[9].m_obj;
lean_object* v___y_750_ = stack[10].m_obj;
lean_object* v_res_796_;
v_res_796_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(v_upperBound_740_, v___x_741_, v_val_742_, v_e_743_, v_isTarget_744_, v_a_745_, v_b_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
stack->m_obj
 = v_res_796_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg___boxed(lean_object* v_upperBound_797_, lean_object* v___x_798_, lean_object* v_val_799_, lean_object* v_e_800_, lean_object* v_isTarget_801_, lean_object* v_a_802_, lean_object* v_b_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(v_upperBound_797_, v___x_798_, v_val_799_, v_e_800_, v_isTarget_801_, v_a_802_, v_b_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec_ref(v_isTarget_801_);
lean_dec_ref(v_e_800_);
lean_dec_ref(v___x_798_);
lean_dec(v_upperBound_797_);
return v_res_809_;
}
}
static lean_object* _init_l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0(void){
_start:
{
lean_object* v___x_810_; lean_object* v_dummy_811_; 
v___x_810_ = lean_box(0);
v_dummy_811_ = l_Lean_Expr_sort___override(v___x_810_);
return v_dummy_811_;
}
}
lean_object* l_Lean_Meta_setMVarUserNamesAt___lam__0(lean_object* v_val_812_, lean_object* v_isTarget_813_, lean_object* v___x_814_, lean_object* v_e_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
uint8_t v___x_821_; 
v___x_821_ = l_Lean_Expr_isApp(v_e_815_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; lean_object* v___x_823_; 
lean_dec_ref(v_e_815_);
lean_dec(v___x_814_);
lean_dec(v_val_812_);
v___x_822_ = lean_box(0);
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
else
{
lean_object* v_dummy_824_; lean_object* v_nargs_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v_dummy_824_ = lean_obj_once(&l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0, &l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0_once, _init_l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0);
v_nargs_825_ = l_Lean_Expr_getAppNumArgs(v_e_815_);
lean_inc(v_nargs_825_);
v___x_826_ = lean_mk_array(v_nargs_825_, v_dummy_824_);
v___x_827_ = lean_unsigned_to_nat(1u);
v___x_828_ = lean_nat_sub(v_nargs_825_, v___x_827_);
lean_dec(v_nargs_825_);
lean_inc_ref(v_e_815_);
v___x_829_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_815_, v___x_826_, v___x_828_);
v___x_830_ = lean_array_get_size(v___x_829_);
v___x_831_ = lean_box(0);
v___x_832_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(v___x_830_, v___x_829_, v_val_812_, v_e_815_, v_isTarget_813_, v___x_814_, v___x_831_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec_ref(v_e_815_);
lean_dec_ref(v___x_829_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; 
v_unused_840_ = lean_ctor_get(v___x_832_, 0);
lean_dec(v_unused_840_);
v___x_834_ = v___x_832_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_dec(v___x_832_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_831_);
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_831_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
else
{
return v___x_832_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_setMVarUserNamesAt___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_812_ = stack[0].m_obj;
lean_object* v_isTarget_813_ = stack[1].m_obj;
lean_object* v___x_814_ = stack[2].m_obj;
lean_object* v_e_815_ = stack[3].m_obj;
lean_object* v___y_816_ = stack[4].m_obj;
lean_object* v___y_817_ = stack[5].m_obj;
lean_object* v___y_818_ = stack[6].m_obj;
lean_object* v___y_819_ = stack[7].m_obj;
lean_object* v_res_841_;
v_res_841_ = l_Lean_Meta_setMVarUserNamesAt___lam__0(v_val_812_, v_isTarget_813_, v___x_814_, v_e_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
stack->m_obj
 = v_res_841_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___lam__0___boxed(lean_object* v_val_842_, lean_object* v_isTarget_843_, lean_object* v___x_844_, lean_object* v_e_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_Meta_setMVarUserNamesAt___lam__0(v_val_842_, v_isTarget_843_, v___x_844_, v_e_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec_ref(v_isTarget_843_);
return v_res_851_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0(lean_object* v_k_852_, lean_object* v___y_853_, lean_object* v_b_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; 
lean_inc(v___y_858_);
lean_inc_ref(v___y_857_);
lean_inc(v___y_856_);
lean_inc_ref(v___y_855_);
lean_inc(v___y_853_);
v___x_860_ = lean_apply_7(v_k_852_, v_b_854_, v___y_853_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, lean_box(0));
return v___x_860_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_852_ = stack[0].m_obj;
lean_object* v___y_853_ = stack[1].m_obj;
lean_object* v_b_854_ = stack[2].m_obj;
lean_object* v___y_855_ = stack[3].m_obj;
lean_object* v___y_856_ = stack[4].m_obj;
lean_object* v___y_857_ = stack[5].m_obj;
lean_object* v___y_858_ = stack[6].m_obj;
lean_object* v_res_861_;
v_res_861_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0(v_k_852_, v___y_853_, v_b_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
stack->m_obj
 = v_res_861_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0___boxed(lean_object* v_k_862_, lean_object* v___y_863_, lean_object* v_b_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0(v_k_862_, v___y_863_, v_b_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_863_);
return v_res_870_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(lean_object* v_name_871_, uint8_t v_bi_872_, lean_object* v_type_873_, lean_object* v_k_874_, uint8_t v_kind_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___f_882_; lean_object* v___x_883_; 
lean_inc(v___y_876_);
v___f_882_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_882_, 0, v_k_874_);
lean_closure_set(v___f_882_, 1, v___y_876_);
v___x_883_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_871_, v_bi_872_, v_type_873_, v___f_882_, v_kind_875_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
if (lean_obj_tag(v___x_883_) == 0)
{
return v___x_883_;
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_871_ = stack[0].m_obj;
uint8_t v_bi_872_ = stack[1].m_num;
lean_object* v_type_873_ = stack[2].m_obj;
lean_object* v_k_874_ = stack[3].m_obj;
uint8_t v_kind_875_ = stack[4].m_num;
lean_object* v___y_876_ = stack[5].m_obj;
lean_object* v___y_877_ = stack[6].m_obj;
lean_object* v___y_878_ = stack[7].m_obj;
lean_object* v___y_879_ = stack[8].m_obj;
lean_object* v___y_880_ = stack[9].m_obj;
lean_object* v_res_892_;
v_res_892_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_name_871_, v_bi_872_, v_type_873_, v_k_874_, v_kind_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
stack->m_obj
 = v_res_892_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___boxed(lean_object* v_name_893_, lean_object* v_bi_894_, lean_object* v_type_895_, lean_object* v_k_896_, lean_object* v_kind_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
uint8_t v_bi_boxed_904_; uint8_t v_kind_boxed_905_; lean_object* v_res_906_; 
v_bi_boxed_904_ = lean_unbox(v_bi_894_);
v_kind_boxed_905_ = lean_unbox(v_kind_897_);
v_res_906_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_name_893_, v_bi_boxed_904_, v_type_895_, v_k_896_, v_kind_boxed_905_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0___boxed(lean_object* v_fvars_907_, lean_object* v_f_908_, lean_object* v_body_909_, lean_object* v_x_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0(v_fvars_907_, v_f_908_, v_body_909_, v_x_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
return v_res_917_;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(lean_object* v_f_918_, lean_object* v_fvars_919_, lean_object* v_a_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
if (lean_obj_tag(v_a_920_) == 6)
{
lean_object* v_binderName_927_; lean_object* v_binderType_928_; lean_object* v_body_929_; uint8_t v_binderInfo_930_; lean_object* v___f_931_; lean_object* v_d_932_; lean_object* v___x_933_; 
v_binderName_927_ = lean_ctor_get(v_a_920_, 0);
lean_inc(v_binderName_927_);
v_binderType_928_ = lean_ctor_get(v_a_920_, 1);
lean_inc_ref(v_binderType_928_);
v_body_929_ = lean_ctor_get(v_a_920_, 2);
lean_inc_ref(v_body_929_);
v_binderInfo_930_ = lean_ctor_get_uint8(v_a_920_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_920_, 3);
lean_inc_ref(v_f_918_);
lean_inc_ref(v_fvars_919_);
v___f_931_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0___boxed), 10, 3);
lean_closure_set(v___f_931_, 0, v_fvars_919_);
lean_closure_set(v___f_931_, 1, v_f_918_);
lean_closure_set(v___f_931_, 2, v_body_929_);
v_d_932_ = lean_expr_instantiate_rev(v_binderType_928_, v_fvars_919_);
lean_dec_ref(v_fvars_919_);
lean_dec_ref(v_binderType_928_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
lean_inc(v___y_921_);
lean_inc_ref(v_d_932_);
v___x_933_ = lean_apply_7(v_f_918_, v_d_932_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, lean_box(0));
if (lean_obj_tag(v___x_933_) == 0)
{
uint8_t v___x_934_; lean_object* v___x_935_; 
lean_dec_ref_known(v___x_933_, 1);
v___x_934_ = 0;
v___x_935_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_binderName_927_, v_binderInfo_930_, v_d_932_, v___f_931_, v___x_934_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
return v___x_935_;
}
else
{
lean_dec_ref(v_d_932_);
lean_dec_ref(v___f_931_);
lean_dec(v_binderName_927_);
return v___x_933_;
}
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = lean_expr_instantiate_rev(v_a_920_, v_fvars_919_);
lean_dec_ref(v_fvars_919_);
lean_dec_ref(v_a_920_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
lean_inc(v___y_921_);
v___x_937_ = lean_apply_7(v_f_918_, v___x_936_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, lean_box(0));
return v___x_937_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_918_ = stack[0].m_obj;
lean_object* v_fvars_919_ = stack[1].m_obj;
lean_object* v_a_920_ = stack[2].m_obj;
lean_object* v___y_921_ = stack[3].m_obj;
lean_object* v___y_922_ = stack[4].m_obj;
lean_object* v___y_923_ = stack[5].m_obj;
lean_object* v___y_924_ = stack[6].m_obj;
lean_object* v___y_925_ = stack[7].m_obj;
lean_object* v_res_938_;
v_res_938_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(v_f_918_, v_fvars_919_, v_a_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
stack->m_obj
 = v_res_938_;
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0(lean_object* v_fvars_939_, lean_object* v_f_940_, lean_object* v_body_941_, lean_object* v_x_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = lean_array_push(v_fvars_939_, v_x_942_);
v___x_950_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(v_f_940_, v___x_949_, v_body_941_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
return v___x_950_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_939_ = stack[0].m_obj;
lean_object* v_f_940_ = stack[1].m_obj;
lean_object* v_body_941_ = stack[2].m_obj;
lean_object* v_x_942_ = stack[3].m_obj;
lean_object* v___y_943_ = stack[4].m_obj;
lean_object* v___y_944_ = stack[5].m_obj;
lean_object* v___y_945_ = stack[6].m_obj;
lean_object* v___y_946_ = stack[7].m_obj;
lean_object* v___y_947_ = stack[8].m_obj;
lean_object* v_res_951_;
v_res_951_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___lam__0(v_fvars_939_, v_f_940_, v_body_941_, v_x_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
stack->m_obj
 = v_res_951_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16___boxed(lean_object* v_f_952_, lean_object* v_fvars_953_, lean_object* v_a_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(v_f_952_, v_fvars_953_, v_a_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
return v_res_961_;
}
}
lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(lean_object* v_f_962_, lean_object* v_e_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_971_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_spec__16(v_f_962_, v___x_970_, v_e_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
return v___x_971_;
}
}
LEAN_EXPORT void l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_962_ = stack[0].m_obj;
lean_object* v_e_963_ = stack[1].m_obj;
lean_object* v___y_964_ = stack[2].m_obj;
lean_object* v___y_965_ = stack[3].m_obj;
lean_object* v___y_966_ = stack[4].m_obj;
lean_object* v___y_967_ = stack[5].m_obj;
lean_object* v___y_968_ = stack[6].m_obj;
lean_object* v_res_972_;
v_res_972_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(v_f_962_, v_e_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
stack->m_obj
 = v_res_972_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10___boxed(lean_object* v_f_973_, lean_object* v_e_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(v_f_973_, v_e_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
return v_res_981_;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_object* v_00_u03b1_982_, lean_object* v_x_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_apply_1(v_x_983_, lean_box(0));
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_983_ = stack[1].m_obj;
lean_object* v___y_984_ = stack[2].m_obj;
lean_object* v___y_985_ = stack[3].m_obj;
lean_object* v___y_986_ = stack[4].m_obj;
lean_object* v___y_987_ = stack[5].m_obj;
lean_object* v_res_991_;
v_res_991_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_box(0), v_x_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
stack->m_obj
 = v_res_991_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0___boxed(lean_object* v_00_u03b1_992_, lean_object* v_x_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(v_00_u03b1_992_, v_x_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0___boxed(lean_object* v_fvars_1000_, lean_object* v_f_1001_, lean_object* v_body_1002_, lean_object* v_x_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0(v_fvars_1000_, v_f_1001_, v_body_1002_, v_x_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
return v_res_1010_;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(lean_object* v_f_1011_, lean_object* v_fvars_1012_, lean_object* v_a_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
if (lean_obj_tag(v_a_1013_) == 7)
{
lean_object* v_binderName_1020_; lean_object* v_binderType_1021_; lean_object* v_body_1022_; uint8_t v_binderInfo_1023_; lean_object* v___f_1024_; lean_object* v_d_1025_; lean_object* v___x_1026_; 
v_binderName_1020_ = lean_ctor_get(v_a_1013_, 0);
lean_inc(v_binderName_1020_);
v_binderType_1021_ = lean_ctor_get(v_a_1013_, 1);
lean_inc_ref(v_binderType_1021_);
v_body_1022_ = lean_ctor_get(v_a_1013_, 2);
lean_inc_ref(v_body_1022_);
v_binderInfo_1023_ = lean_ctor_get_uint8(v_a_1013_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_1013_, 3);
lean_inc_ref(v_f_1011_);
lean_inc_ref(v_fvars_1012_);
v___f_1024_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1024_, 0, v_fvars_1012_);
lean_closure_set(v___f_1024_, 1, v_f_1011_);
lean_closure_set(v___f_1024_, 2, v_body_1022_);
v_d_1025_ = lean_expr_instantiate_rev(v_binderType_1021_, v_fvars_1012_);
lean_dec_ref(v_fvars_1012_);
lean_dec_ref(v_binderType_1021_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
lean_inc(v___y_1016_);
lean_inc_ref(v___y_1015_);
lean_inc(v___y_1014_);
lean_inc_ref(v_d_1025_);
v___x_1026_ = lean_apply_7(v_f_1011_, v_d_1025_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, lean_box(0));
if (lean_obj_tag(v___x_1026_) == 0)
{
uint8_t v___x_1027_; lean_object* v___x_1028_; 
lean_dec_ref_known(v___x_1026_, 1);
v___x_1027_ = 0;
v___x_1028_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_binderName_1020_, v_binderInfo_1023_, v_d_1025_, v___f_1024_, v___x_1027_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
return v___x_1028_;
}
else
{
lean_dec_ref(v_d_1025_);
lean_dec_ref(v___f_1024_);
lean_dec(v_binderName_1020_);
return v___x_1026_;
}
}
else
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_expr_instantiate_rev(v_a_1013_, v_fvars_1012_);
lean_dec_ref(v_fvars_1012_);
lean_dec_ref(v_a_1013_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
lean_inc(v___y_1016_);
lean_inc_ref(v___y_1015_);
lean_inc(v___y_1014_);
v___x_1030_ = lean_apply_7(v_f_1011_, v___x_1029_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, lean_box(0));
return v___x_1030_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1011_ = stack[0].m_obj;
lean_object* v_fvars_1012_ = stack[1].m_obj;
lean_object* v_a_1013_ = stack[2].m_obj;
lean_object* v___y_1014_ = stack[3].m_obj;
lean_object* v___y_1015_ = stack[4].m_obj;
lean_object* v___y_1016_ = stack[5].m_obj;
lean_object* v___y_1017_ = stack[6].m_obj;
lean_object* v___y_1018_ = stack[7].m_obj;
lean_object* v_res_1031_;
v_res_1031_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(v_f_1011_, v_fvars_1012_, v_a_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
stack->m_obj
 = v_res_1031_;
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0(lean_object* v_fvars_1032_, lean_object* v_f_1033_, lean_object* v_body_1034_, lean_object* v_x_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_array_push(v_fvars_1032_, v_x_1035_);
v___x_1043_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(v_f_1033_, v___x_1042_, v_body_1034_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
return v___x_1043_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1032_ = stack[0].m_obj;
lean_object* v_f_1033_ = stack[1].m_obj;
lean_object* v_body_1034_ = stack[2].m_obj;
lean_object* v_x_1035_ = stack[3].m_obj;
lean_object* v___y_1036_ = stack[4].m_obj;
lean_object* v___y_1037_ = stack[5].m_obj;
lean_object* v___y_1038_ = stack[6].m_obj;
lean_object* v___y_1039_ = stack[7].m_obj;
lean_object* v___y_1040_ = stack[8].m_obj;
lean_object* v_res_1044_;
v_res_1044_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___lam__0(v_fvars_1032_, v_f_1033_, v_body_1034_, v_x_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
stack->m_obj
 = v_res_1044_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14___boxed(lean_object* v_f_1045_, lean_object* v_fvars_1046_, lean_object* v_a_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(v_f_1045_, v_fvars_1046_, v_a_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
return v_res_1054_;
}
}
lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(lean_object* v_f_1055_, lean_object* v_e_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_1064_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14(v_f_1055_, v___x_1063_, v_e_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
return v___x_1064_;
}
}
LEAN_EXPORT void l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1055_ = stack[0].m_obj;
lean_object* v_e_1056_ = stack[1].m_obj;
lean_object* v___y_1057_ = stack[2].m_obj;
lean_object* v___y_1058_ = stack[3].m_obj;
lean_object* v___y_1059_ = stack[4].m_obj;
lean_object* v___y_1060_ = stack[5].m_obj;
lean_object* v___y_1061_ = stack[6].m_obj;
lean_object* v_res_1065_;
v_res_1065_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(v_f_1055_, v_e_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
stack->m_obj
 = v_res_1065_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9___boxed(lean_object* v_f_1066_, lean_object* v_e_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(v_f_1066_, v_e_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(lean_object* v_a_1075_, lean_object* v_x_1076_){
_start:
{
if (lean_obj_tag(v_x_1076_) == 0)
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_box(0);
return v___x_1077_;
}
else
{
lean_object* v_key_1078_; lean_object* v_value_1079_; lean_object* v_tail_1080_; uint8_t v___x_1081_; 
v_key_1078_ = lean_ctor_get(v_x_1076_, 0);
v_value_1079_ = lean_ctor_get(v_x_1076_, 1);
v_tail_1080_ = lean_ctor_get(v_x_1076_, 2);
v___x_1081_ = lean_expr_eqv(v_key_1078_, v_a_1075_);
if (v___x_1081_ == 0)
{
v_x_1076_ = v_tail_1080_;
goto _start;
}
else
{
lean_object* v___x_1083_; 
lean_inc(v_value_1079_);
v___x_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1083_, 0, v_value_1079_);
return v___x_1083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_a_1084_, lean_object* v_x_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(v_a_1084_, v_x_1085_);
lean_dec(v_x_1085_);
lean_dec_ref(v_a_1084_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(lean_object* v_m_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v_buckets_1089_; lean_object* v___x_1090_; uint64_t v___x_1091_; uint64_t v___x_1092_; uint64_t v___x_1093_; uint64_t v_fold_1094_; uint64_t v___x_1095_; uint64_t v___x_1096_; uint64_t v___x_1097_; size_t v___x_1098_; size_t v___x_1099_; size_t v___x_1100_; size_t v___x_1101_; size_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v_buckets_1089_ = lean_ctor_get(v_m_1087_, 1);
v___x_1090_ = lean_array_get_size(v_buckets_1089_);
v___x_1091_ = l_Lean_Expr_hash(v_a_1088_);
v___x_1092_ = 32ULL;
v___x_1093_ = lean_uint64_shift_right(v___x_1091_, v___x_1092_);
v_fold_1094_ = lean_uint64_xor(v___x_1091_, v___x_1093_);
v___x_1095_ = 16ULL;
v___x_1096_ = lean_uint64_shift_right(v_fold_1094_, v___x_1095_);
v___x_1097_ = lean_uint64_xor(v_fold_1094_, v___x_1096_);
v___x_1098_ = lean_uint64_to_usize(v___x_1097_);
v___x_1099_ = lean_usize_of_nat(v___x_1090_);
v___x_1100_ = ((size_t)1ULL);
v___x_1101_ = lean_usize_sub(v___x_1099_, v___x_1100_);
v___x_1102_ = lean_usize_land(v___x_1098_, v___x_1101_);
v___x_1103_ = lean_array_uget_borrowed(v_buckets_1089_, v___x_1102_);
v___x_1104_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(v_a_1088_, v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_m_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_m_1105_, v_a_1106_);
lean_dec_ref(v_a_1106_);
lean_dec_ref(v_m_1105_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(lean_object* v_a_1108_, lean_object* v_b_1109_, lean_object* v_x_1110_){
_start:
{
if (lean_obj_tag(v_x_1110_) == 0)
{
lean_dec(v_b_1109_);
lean_dec_ref(v_a_1108_);
return v_x_1110_;
}
else
{
lean_object* v_key_1111_; lean_object* v_value_1112_; lean_object* v_tail_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1125_; 
v_key_1111_ = lean_ctor_get(v_x_1110_, 0);
v_value_1112_ = lean_ctor_get(v_x_1110_, 1);
v_tail_1113_ = lean_ctor_get(v_x_1110_, 2);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_x_1110_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1115_ = v_x_1110_;
v_isShared_1116_ = v_isSharedCheck_1125_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_tail_1113_);
lean_inc(v_value_1112_);
lean_inc(v_key_1111_);
lean_dec(v_x_1110_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1125_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
uint8_t v___x_1117_; 
v___x_1117_ = lean_expr_eqv(v_key_1111_, v_a_1108_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
v___x_1118_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(v_a_1108_, v_b_1109_, v_tail_1113_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 2, v___x_1118_);
v___x_1120_ = v___x_1115_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_key_1111_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_value_1112_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
else
{
lean_object* v___x_1123_; 
lean_dec(v_value_1112_);
lean_dec(v_key_1111_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 1, v_b_1109_);
lean_ctor_set(v___x_1115_, 0, v_a_1108_);
v___x_1123_ = v___x_1115_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1108_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_b_1109_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v_tail_1113_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16___redArg(lean_object* v_x_1126_, lean_object* v_x_1127_){
_start:
{
if (lean_obj_tag(v_x_1127_) == 0)
{
return v_x_1126_;
}
else
{
lean_object* v_key_1128_; lean_object* v_value_1129_; lean_object* v_tail_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1153_; 
v_key_1128_ = lean_ctor_get(v_x_1127_, 0);
v_value_1129_ = lean_ctor_get(v_x_1127_, 1);
v_tail_1130_ = lean_ctor_get(v_x_1127_, 2);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_x_1127_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1132_ = v_x_1127_;
v_isShared_1133_ = v_isSharedCheck_1153_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_tail_1130_);
lean_inc(v_value_1129_);
lean_inc(v_key_1128_);
lean_dec(v_x_1127_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1153_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; uint64_t v___x_1135_; uint64_t v___x_1136_; uint64_t v___x_1137_; uint64_t v_fold_1138_; uint64_t v___x_1139_; uint64_t v___x_1140_; uint64_t v___x_1141_; size_t v___x_1142_; size_t v___x_1143_; size_t v___x_1144_; size_t v___x_1145_; size_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1134_ = lean_array_get_size(v_x_1126_);
v___x_1135_ = l_Lean_Expr_hash(v_key_1128_);
v___x_1136_ = 32ULL;
v___x_1137_ = lean_uint64_shift_right(v___x_1135_, v___x_1136_);
v_fold_1138_ = lean_uint64_xor(v___x_1135_, v___x_1137_);
v___x_1139_ = 16ULL;
v___x_1140_ = lean_uint64_shift_right(v_fold_1138_, v___x_1139_);
v___x_1141_ = lean_uint64_xor(v_fold_1138_, v___x_1140_);
v___x_1142_ = lean_uint64_to_usize(v___x_1141_);
v___x_1143_ = lean_usize_of_nat(v___x_1134_);
v___x_1144_ = ((size_t)1ULL);
v___x_1145_ = lean_usize_sub(v___x_1143_, v___x_1144_);
v___x_1146_ = lean_usize_land(v___x_1142_, v___x_1145_);
v___x_1147_ = lean_array_uget_borrowed(v_x_1126_, v___x_1146_);
lean_inc(v___x_1147_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 2, v___x_1147_);
v___x_1149_ = v___x_1132_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_key_1128_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_value_1129_);
lean_ctor_set(v_reuseFailAlloc_1152_, 2, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1150_; 
v___x_1150_ = lean_array_uset(v_x_1126_, v___x_1146_, v___x_1149_);
v_x_1126_ = v___x_1150_;
v_x_1127_ = v_tail_1130_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12___redArg(lean_object* v_i_1154_, lean_object* v_source_1155_, lean_object* v_target_1156_){
_start:
{
lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = lean_array_get_size(v_source_1155_);
v___x_1158_ = lean_nat_dec_lt(v_i_1154_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_dec_ref(v_source_1155_);
lean_dec(v_i_1154_);
return v_target_1156_;
}
else
{
lean_object* v_es_1159_; lean_object* v___x_1160_; lean_object* v_source_1161_; lean_object* v_target_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v_es_1159_ = lean_array_fget(v_source_1155_, v_i_1154_);
v___x_1160_ = lean_box(0);
v_source_1161_ = lean_array_fset(v_source_1155_, v_i_1154_, v___x_1160_);
v_target_1162_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16___redArg(v_target_1156_, v_es_1159_);
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_nat_add(v_i_1154_, v___x_1163_);
lean_dec(v_i_1154_);
v_i_1154_ = v___x_1164_;
v_source_1155_ = v_source_1161_;
v_target_1156_ = v_target_1162_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11___redArg(lean_object* v_data_1166_){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v_nbuckets_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1167_ = lean_array_get_size(v_data_1166_);
v___x_1168_ = lean_unsigned_to_nat(2u);
v_nbuckets_1169_ = lean_nat_mul(v___x_1167_, v___x_1168_);
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = lean_box(0);
v___x_1172_ = lean_mk_array(v_nbuckets_1169_, v___x_1171_);
v___x_1173_ = lean_array_propagate_mark(v_data_1166_, v___x_1172_);
v___x_1174_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12___redArg(v___x_1170_, v_data_1166_, v___x_1173_);
return v___x_1174_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(lean_object* v_a_1175_, lean_object* v_x_1176_){
_start:
{
if (lean_obj_tag(v_x_1176_) == 0)
{
uint8_t v___x_1177_; 
v___x_1177_ = 0;
return v___x_1177_;
}
else
{
lean_object* v_key_1178_; lean_object* v_tail_1179_; uint8_t v___x_1180_; 
v_key_1178_ = lean_ctor_get(v_x_1176_, 0);
v_tail_1179_ = lean_ctor_get(v_x_1176_, 2);
v___x_1180_ = lean_expr_eqv(v_key_1178_, v_a_1175_);
if (v___x_1180_ == 0)
{
v_x_1176_ = v_tail_1179_;
goto _start;
}
else
{
return v___x_1180_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1175_ = stack[0].m_obj;
lean_object* v_x_1176_ = stack[1].m_obj;
uint8_t v_res_1182_;
v_res_1182_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_a_1175_, v_x_1176_);
stack->m_num = v_res_1182_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_a_1183_, lean_object* v_x_1184_){
_start:
{
uint8_t v_res_1185_; lean_object* v_r_1186_; 
v_res_1185_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_a_1183_, v_x_1184_);
lean_dec(v_x_1184_);
lean_dec_ref(v_a_1183_);
v_r_1186_ = lean_box(v_res_1185_);
return v_r_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(lean_object* v_m_1187_, lean_object* v_a_1188_, lean_object* v_b_1189_){
_start:
{
lean_object* v_size_1190_; lean_object* v_buckets_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1234_; 
v_size_1190_ = lean_ctor_get(v_m_1187_, 0);
v_buckets_1191_ = lean_ctor_get(v_m_1187_, 1);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_m_1187_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1193_ = v_m_1187_;
v_isShared_1194_ = v_isSharedCheck_1234_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_buckets_1191_);
lean_inc(v_size_1190_);
lean_dec(v_m_1187_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1234_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; uint64_t v___x_1196_; uint64_t v___x_1197_; uint64_t v___x_1198_; uint64_t v_fold_1199_; uint64_t v___x_1200_; uint64_t v___x_1201_; uint64_t v___x_1202_; size_t v___x_1203_; size_t v___x_1204_; size_t v___x_1205_; size_t v___x_1206_; size_t v___x_1207_; lean_object* v_bkt_1208_; uint8_t v___x_1209_; 
v___x_1195_ = lean_array_get_size(v_buckets_1191_);
v___x_1196_ = l_Lean_Expr_hash(v_a_1188_);
v___x_1197_ = 32ULL;
v___x_1198_ = lean_uint64_shift_right(v___x_1196_, v___x_1197_);
v_fold_1199_ = lean_uint64_xor(v___x_1196_, v___x_1198_);
v___x_1200_ = 16ULL;
v___x_1201_ = lean_uint64_shift_right(v_fold_1199_, v___x_1200_);
v___x_1202_ = lean_uint64_xor(v_fold_1199_, v___x_1201_);
v___x_1203_ = lean_uint64_to_usize(v___x_1202_);
v___x_1204_ = lean_usize_of_nat(v___x_1195_);
v___x_1205_ = ((size_t)1ULL);
v___x_1206_ = lean_usize_sub(v___x_1204_, v___x_1205_);
v___x_1207_ = lean_usize_land(v___x_1203_, v___x_1206_);
v_bkt_1208_ = lean_array_uget_borrowed(v_buckets_1191_, v___x_1207_);
v___x_1209_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_a_1188_, v_bkt_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; lean_object* v_size_x27_1211_; lean_object* v___x_1212_; lean_object* v_buckets_x27_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1210_ = lean_unsigned_to_nat(1u);
v_size_x27_1211_ = lean_nat_add(v_size_1190_, v___x_1210_);
lean_dec(v_size_1190_);
lean_inc(v_bkt_1208_);
v___x_1212_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1212_, 0, v_a_1188_);
lean_ctor_set(v___x_1212_, 1, v_b_1189_);
lean_ctor_set(v___x_1212_, 2, v_bkt_1208_);
v_buckets_x27_1213_ = lean_array_uset(v_buckets_1191_, v___x_1207_, v___x_1212_);
v___x_1214_ = lean_unsigned_to_nat(4u);
v___x_1215_ = lean_nat_mul(v_size_x27_1211_, v___x_1214_);
v___x_1216_ = lean_unsigned_to_nat(3u);
v___x_1217_ = lean_nat_div(v___x_1215_, v___x_1216_);
lean_dec(v___x_1215_);
v___x_1218_ = lean_array_get_size(v_buckets_x27_1213_);
v___x_1219_ = lean_nat_dec_le(v___x_1217_, v___x_1218_);
lean_dec(v___x_1217_);
if (v___x_1219_ == 0)
{
lean_object* v_val_1220_; lean_object* v___x_1222_; 
v_val_1220_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11___redArg(v_buckets_x27_1213_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v_val_1220_);
lean_ctor_set(v___x_1193_, 0, v_size_x27_1211_);
v___x_1222_ = v___x_1193_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_size_x27_1211_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_val_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
else
{
lean_object* v___x_1225_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v_buckets_x27_1213_);
lean_ctor_set(v___x_1193_, 0, v_size_x27_1211_);
v___x_1225_ = v___x_1193_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_size_x27_1211_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_buckets_x27_1213_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
else
{
lean_object* v___x_1227_; lean_object* v_buckets_x27_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1232_; 
lean_inc(v_bkt_1208_);
v___x_1227_ = lean_box(0);
v_buckets_x27_1228_ = lean_array_uset(v_buckets_1191_, v___x_1207_, v___x_1227_);
v___x_1229_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(v_a_1188_, v_b_1189_, v_bkt_1208_);
v___x_1230_ = lean_array_uset(v_buckets_x27_1228_, v___x_1207_, v___x_1229_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v___x_1230_);
v___x_1232_ = v___x_1193_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_size_1190_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1(lean_object* v_a_1235_, lean_object* v_e_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1239_ = lean_st_ref_take(v_a_1235_);
v___x_1240_ = lean_box(0);
v___x_1241_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(v___x_1239_, v_e_1236_, v_a_1237_);
v___x_1242_ = lean_st_ref_put(v_a_1235_, v___x_1241_);
return v___x_1240_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1235_ = stack[0].m_obj;
lean_object* v_e_1236_ = stack[1].m_obj;
lean_object* v_a_1237_ = stack[2].m_obj;
lean_object* v_res_1243_;
v_res_1243_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1(v_a_1235_, v_e_1236_, v_a_1237_);
stack->m_obj
 = v_res_1243_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_a_1244_, lean_object* v_e_1245_, lean_object* v_a_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1(v_a_1244_, v_e_1245_, v_a_1246_);
lean_dec(v_a_1244_);
return v_res_1248_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(lean_object* v_name_1249_, lean_object* v_type_1250_, lean_object* v_val_1251_, lean_object* v_k_1252_, uint8_t v_nondep_1253_, uint8_t v_kind_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___f_1261_; lean_object* v___x_1262_; 
lean_inc(v___y_1255_);
v___f_1261_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1261_, 0, v_k_1252_);
lean_closure_set(v___f_1261_, 1, v___y_1255_);
v___x_1262_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1249_, v_type_1250_, v_val_1251_, v___f_1261_, v_nondep_1253_, v_kind_1254_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
if (lean_obj_tag(v___x_1262_) == 0)
{
return v___x_1262_;
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1249_ = stack[0].m_obj;
lean_object* v_type_1250_ = stack[1].m_obj;
lean_object* v_val_1251_ = stack[2].m_obj;
lean_object* v_k_1252_ = stack[3].m_obj;
uint8_t v_nondep_1253_ = stack[4].m_num;
uint8_t v_kind_1254_ = stack[5].m_num;
lean_object* v___y_1255_ = stack[6].m_obj;
lean_object* v___y_1256_ = stack[7].m_obj;
lean_object* v___y_1257_ = stack[8].m_obj;
lean_object* v___y_1258_ = stack[9].m_obj;
lean_object* v___y_1259_ = stack[10].m_obj;
lean_object* v_res_1271_;
v_res_1271_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(v_name_1249_, v_type_1250_, v_val_1251_, v_k_1252_, v_nondep_1253_, v_kind_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
stack->m_obj
 = v_res_1271_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg___boxed(lean_object* v_name_1272_, lean_object* v_type_1273_, lean_object* v_val_1274_, lean_object* v_k_1275_, lean_object* v_nondep_1276_, lean_object* v_kind_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
uint8_t v_nondep_boxed_1284_; uint8_t v_kind_boxed_1285_; lean_object* v_res_1286_; 
v_nondep_boxed_1284_ = lean_unbox(v_nondep_1276_);
v_kind_boxed_1285_ = lean_unbox(v_kind_1277_);
v_res_1286_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(v_name_1272_, v_type_1273_, v_val_1274_, v_k_1275_, v_nondep_boxed_1284_, v_kind_boxed_1285_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0___boxed(lean_object* v_fvars_1287_, lean_object* v_f_1288_, lean_object* v_body_1289_, lean_object* v_x_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0(v_fvars_1287_, v_f_1288_, v_body_1289_, v_x_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
return v_res_1297_;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(lean_object* v_f_1298_, lean_object* v_fvars_1299_, lean_object* v_a_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
if (lean_obj_tag(v_a_1300_) == 8)
{
lean_object* v_declName_1307_; lean_object* v_type_1308_; lean_object* v_value_1309_; lean_object* v_body_1310_; lean_object* v___f_1311_; lean_object* v_d_1312_; lean_object* v_v_1313_; lean_object* v___x_1314_; 
v_declName_1307_ = lean_ctor_get(v_a_1300_, 0);
lean_inc(v_declName_1307_);
v_type_1308_ = lean_ctor_get(v_a_1300_, 1);
lean_inc_ref(v_type_1308_);
v_value_1309_ = lean_ctor_get(v_a_1300_, 2);
lean_inc_ref(v_value_1309_);
v_body_1310_ = lean_ctor_get(v_a_1300_, 3);
lean_inc_ref(v_body_1310_);
lean_dec_ref_known(v_a_1300_, 4);
lean_inc_ref_n(v_f_1298_, 2);
lean_inc_ref(v_fvars_1299_);
v___f_1311_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1311_, 0, v_fvars_1299_);
lean_closure_set(v___f_1311_, 1, v_f_1298_);
lean_closure_set(v___f_1311_, 2, v_body_1310_);
v_d_1312_ = lean_expr_instantiate_rev(v_type_1308_, v_fvars_1299_);
lean_dec_ref(v_type_1308_);
v_v_1313_ = lean_expr_instantiate_rev(v_value_1309_, v_fvars_1299_);
lean_dec_ref(v_fvars_1299_);
lean_dec_ref(v_value_1309_);
lean_inc(v___y_1305_);
lean_inc_ref(v___y_1304_);
lean_inc(v___y_1303_);
lean_inc_ref(v___y_1302_);
lean_inc(v___y_1301_);
lean_inc_ref(v_d_1312_);
v___x_1314_ = lean_apply_7(v_f_1298_, v_d_1312_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, lean_box(0));
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v___x_1315_; 
lean_dec_ref_known(v___x_1314_, 1);
lean_inc(v___y_1305_);
lean_inc_ref(v___y_1304_);
lean_inc(v___y_1303_);
lean_inc_ref(v___y_1302_);
lean_inc(v___y_1301_);
lean_inc_ref(v_v_1313_);
v___x_1315_ = lean_apply_7(v_f_1298_, v_v_1313_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, lean_box(0));
if (lean_obj_tag(v___x_1315_) == 0)
{
uint8_t v___x_1316_; uint8_t v___x_1317_; lean_object* v___x_1318_; 
lean_dec_ref_known(v___x_1315_, 1);
v___x_1316_ = 0;
v___x_1317_ = 0;
v___x_1318_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(v_declName_1307_, v_d_1312_, v_v_1313_, v___f_1311_, v___x_1316_, v___x_1317_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
return v___x_1318_;
}
else
{
lean_dec_ref(v_v_1313_);
lean_dec_ref(v_d_1312_);
lean_dec_ref(v___f_1311_);
lean_dec(v_declName_1307_);
return v___x_1315_;
}
}
else
{
lean_dec_ref(v_v_1313_);
lean_dec_ref(v_d_1312_);
lean_dec_ref(v___f_1311_);
lean_dec(v_declName_1307_);
lean_dec_ref(v_f_1298_);
return v___x_1314_;
}
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = lean_expr_instantiate_rev(v_a_1300_, v_fvars_1299_);
lean_dec_ref(v_fvars_1299_);
lean_dec_ref(v_a_1300_);
lean_inc(v___y_1305_);
lean_inc_ref(v___y_1304_);
lean_inc(v___y_1303_);
lean_inc_ref(v___y_1302_);
lean_inc(v___y_1301_);
v___x_1320_ = lean_apply_7(v_f_1298_, v___x_1319_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, lean_box(0));
return v___x_1320_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1298_ = stack[0].m_obj;
lean_object* v_fvars_1299_ = stack[1].m_obj;
lean_object* v_a_1300_ = stack[2].m_obj;
lean_object* v___y_1301_ = stack[3].m_obj;
lean_object* v___y_1302_ = stack[4].m_obj;
lean_object* v___y_1303_ = stack[5].m_obj;
lean_object* v___y_1304_ = stack[6].m_obj;
lean_object* v___y_1305_ = stack[7].m_obj;
lean_object* v_res_1321_;
v_res_1321_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(v_f_1298_, v_fvars_1299_, v_a_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
stack->m_obj
 = v_res_1321_;
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0(lean_object* v_fvars_1322_, lean_object* v_f_1323_, lean_object* v_body_1324_, lean_object* v_x_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = lean_array_push(v_fvars_1322_, v_x_1325_);
v___x_1333_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(v_f_1323_, v___x_1332_, v_body_1324_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
return v___x_1333_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1322_ = stack[0].m_obj;
lean_object* v_f_1323_ = stack[1].m_obj;
lean_object* v_body_1324_ = stack[2].m_obj;
lean_object* v_x_1325_ = stack[3].m_obj;
lean_object* v___y_1326_ = stack[4].m_obj;
lean_object* v___y_1327_ = stack[5].m_obj;
lean_object* v___y_1328_ = stack[6].m_obj;
lean_object* v___y_1329_ = stack[7].m_obj;
lean_object* v___y_1330_ = stack[8].m_obj;
lean_object* v_res_1334_;
v_res_1334_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0(v_fvars_1322_, v_f_1323_, v_body_1324_, v_x_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
stack->m_obj
 = v_res_1334_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___boxed(lean_object* v_f_1335_, lean_object* v_fvars_1336_, lean_object* v_a_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(v_f_1335_, v_fvars_1336_, v_a_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
return v_res_1344_;
}
}
lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(lean_object* v_f_1345_, lean_object* v_e_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_1354_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(v_f_1345_, v___x_1353_, v_e_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
return v___x_1354_;
}
}
LEAN_EXPORT void l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1345_ = stack[0].m_obj;
lean_object* v_e_1346_ = stack[1].m_obj;
lean_object* v___y_1347_ = stack[2].m_obj;
lean_object* v___y_1348_ = stack[3].m_obj;
lean_object* v___y_1349_ = stack[4].m_obj;
lean_object* v___y_1350_ = stack[5].m_obj;
lean_object* v___y_1351_ = stack[6].m_obj;
lean_object* v_res_1355_;
v_res_1355_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(v_f_1345_, v_e_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
stack->m_obj
 = v_res_1355_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11___boxed(lean_object* v_f_1356_, lean_object* v_e_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(v_f_1356_, v_e_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed(lean_object* v_fn_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2(v_fn_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
return v_res_1373_;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(lean_object* v_fn_1374_, lean_object* v_e_1375_, lean_object* v_a_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
lean_object* v_a_1383_; lean_object* v___y_1395_; lean_object* v___f_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_inc_ref(v_fn_1374_);
v___f_1397_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1397_, 0, v_fn_1374_);
lean_inc(v_a_1376_);
v___x_1398_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1398_, 0, lean_box(0));
lean_closure_set(v___x_1398_, 1, lean_box(0));
lean_closure_set(v___x_1398_, 2, v_a_1376_);
v___x_1399_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_box(0), v___x_1398_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1399_) == 0)
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1433_; 
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1433_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1433_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_a_1400_, v_e_1375_);
lean_dec(v_a_1400_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v___x_1405_; 
lean_del_object(v___x_1402_);
lean_inc_ref(v_fn_1374_);
lean_inc(v___y_1380_);
lean_inc_ref(v___y_1379_);
lean_inc(v___y_1378_);
lean_inc_ref(v___y_1377_);
lean_inc_ref(v_e_1375_);
v___x_1405_ = lean_apply_6(v_fn_1374_, v_e_1375_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, lean_box(0));
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; uint8_t v___x_1407_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1405_, 1);
v___x_1407_ = lean_unbox(v_a_1406_);
lean_dec(v_a_1406_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; 
lean_dec_ref(v___f_1397_);
lean_dec_ref(v_fn_1374_);
v___x_1408_ = lean_box(0);
v_a_1383_ = v___x_1408_;
goto v___jp_1382_;
}
else
{
switch(lean_obj_tag(v_e_1375_))
{
case 7:
{
lean_object* v___x_1409_; 
lean_dec_ref(v_fn_1374_);
lean_inc_ref(v_e_1375_);
v___x_1409_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(v___f_1397_, v_e_1375_, v_a_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
v___y_1395_ = v___x_1409_;
goto v___jp_1394_;
}
case 6:
{
lean_object* v___x_1410_; 
lean_dec_ref(v_fn_1374_);
lean_inc_ref(v_e_1375_);
v___x_1410_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(v___f_1397_, v_e_1375_, v_a_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
v___y_1395_ = v___x_1410_;
goto v___jp_1394_;
}
case 8:
{
lean_object* v___x_1411_; 
lean_dec_ref(v_fn_1374_);
lean_inc_ref(v_e_1375_);
v___x_1411_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(v___f_1397_, v_e_1375_, v_a_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
v___y_1395_ = v___x_1411_;
goto v___jp_1394_;
}
case 5:
{
lean_object* v_fn_1412_; lean_object* v_arg_1413_; lean_object* v___x_1414_; 
lean_dec_ref(v___f_1397_);
v_fn_1412_ = lean_ctor_get(v_e_1375_, 0);
v_arg_1413_ = lean_ctor_get(v_e_1375_, 1);
lean_inc_ref(v_fn_1412_);
lean_inc_ref(v_fn_1374_);
v___x_1414_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1374_, v_fn_1412_, v_a_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v___x_1415_; 
lean_dec_ref_known(v___x_1414_, 1);
lean_inc_ref(v_arg_1413_);
v___x_1415_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1374_, v_arg_1413_, v_a_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
v___y_1395_ = v___x_1415_;
goto v___jp_1394_;
}
else
{
lean_dec_ref(v_fn_1374_);
v___y_1395_ = v___x_1414_;
goto v___jp_1394_;
}
}
case 10:
{
lean_object* v_expr_1416_; lean_object* v___x_1417_; 
lean_dec_ref(v___f_1397_);
v_expr_1416_ = lean_ctor_get(v_e_1375_, 1);
lean_inc_ref(v_expr_1416_);
v___x_1417_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1374_, v_expr_1416_, v_a_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
v___y_1395_ = v___x_1417_;
goto v___jp_1394_;
}
case 11:
{
lean_object* v_struct_1418_; lean_object* v___x_1419_; 
lean_dec_ref(v___f_1397_);
v_struct_1418_ = lean_ctor_get(v_e_1375_, 2);
lean_inc_ref(v_struct_1418_);
v___x_1419_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1374_, v_struct_1418_, v_a_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
v___y_1395_ = v___x_1419_;
goto v___jp_1394_;
}
default: 
{
lean_object* v___x_1420_; 
lean_dec_ref(v___f_1397_);
lean_dec_ref(v_fn_1374_);
v___x_1420_ = lean_box(0);
v_a_1383_ = v___x_1420_;
goto v___jp_1382_;
}
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec_ref(v___f_1397_);
lean_dec_ref(v_e_1375_);
lean_dec_ref(v_fn_1374_);
v_a_1421_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1405_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1405_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
else
{
lean_object* v_val_1429_; lean_object* v___x_1431_; 
lean_dec_ref(v___f_1397_);
lean_dec_ref(v_e_1375_);
lean_dec_ref(v_fn_1374_);
v_val_1429_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_val_1429_);
lean_dec_ref_known(v___x_1404_, 1);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v_val_1429_);
v___x_1431_ = v___x_1402_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_val_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec_ref(v___f_1397_);
lean_dec_ref(v_e_1375_);
lean_dec_ref(v_fn_1374_);
v_a_1434_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1399_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1399_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
v___jp_1382_:
{
lean_object* v___f_1384_; lean_object* v___x_1385_; 
lean_inc(v_a_1376_);
v___f_1384_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1384_, 0, v_a_1376_);
lean_closure_set(v___f_1384_, 1, v_e_1375_);
lean_closure_set(v___f_1384_, 2, v_a_1383_);
v___x_1385_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_box(0), v___f_1384_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v___x_1385_, 0);
lean_dec(v_unused_1393_);
v___x_1387_ = v___x_1385_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_dec(v___x_1385_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v_a_1383_);
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1383_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
else
{
return v___x_1385_;
}
}
v___jp_1394_:
{
if (lean_obj_tag(v___y_1395_) == 0)
{
lean_object* v_a_1396_; 
v_a_1396_ = lean_ctor_get(v___y_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___y_1395_, 1);
v_a_1383_ = v_a_1396_;
goto v___jp_1382_;
}
else
{
lean_dec_ref(v_e_1375_);
return v___y_1395_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_1374_ = stack[0].m_obj;
lean_object* v_e_1375_ = stack[1].m_obj;
lean_object* v_a_1376_ = stack[2].m_obj;
lean_object* v___y_1377_ = stack[3].m_obj;
lean_object* v___y_1378_ = stack[4].m_obj;
lean_object* v___y_1379_ = stack[5].m_obj;
lean_object* v___y_1380_ = stack[6].m_obj;
lean_object* v_res_1442_;
v_res_1442_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1374_, v_e_1375_, v_a_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
stack->m_obj
 = v_res_1442_;
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2(lean_object* v_fn_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
return v___x_1451_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_1443_ = stack[0].m_obj;
lean_object* v___y_1444_ = stack[1].m_obj;
lean_object* v___y_1445_ = stack[2].m_obj;
lean_object* v___y_1446_ = stack[3].m_obj;
lean_object* v___y_1447_ = stack[4].m_obj;
lean_object* v___y_1448_ = stack[5].m_obj;
lean_object* v___y_1449_ = stack[6].m_obj;
lean_object* v_res_1452_;
v_res_1452_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2(v_fn_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
stack->m_obj
 = v_res_1452_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___boxed(lean_object* v_fn_1453_, lean_object* v_e_1454_, lean_object* v_a_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1453_, v_e_1454_, v_a_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v_a_1455_);
return v_res_1461_;
}
}
lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_object* v_00_u03b1_1462_, lean_object* v_x_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = lean_apply_1(v_x_1463_, lean_box(0));
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT void l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1463_ = stack[1].m_obj;
lean_object* v___y_1464_ = stack[2].m_obj;
lean_object* v___y_1465_ = stack[3].m_obj;
lean_object* v___y_1466_ = stack[4].m_obj;
lean_object* v___y_1467_ = stack[5].m_obj;
lean_object* v_res_1471_;
v_res_1471_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_box(0), v_x_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
stack->m_obj
 = v_res_1471_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0___boxed(lean_object* v_00_u03b1_1472_, lean_object* v_x_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(v_00_u03b1_1472_, v_x_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
return v_res_1479_;
}
}
lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(lean_object* v_input_1480_, lean_object* v_fn_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v_a_1489_; lean_object* v___x_1490_; 
v___x_1487_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___redArg___closed__2, &l_Lean_Meta_forEachExpr_x27___redArg___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__2);
v___x_1488_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_box(0), v___x_1487_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1489_);
lean_dec_ref(v___x_1488_);
v___x_1490_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1481_, v_input_1480_, v_a_1489_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
lean_dec_ref_known(v___x_1490_, 1);
v___x_1492_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1492_, 0, lean_box(0));
lean_closure_set(v___x_1492_, 1, lean_box(0));
lean_closure_set(v___x_1492_, 2, v_a_1489_);
v___x_1493_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_box(0), v___x_1492_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; 
v_unused_1501_ = lean_ctor_get(v___x_1493_, 0);
lean_dec(v_unused_1501_);
v___x_1495_ = v___x_1493_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_dec(v___x_1493_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v_a_1491_);
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1491_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
else
{
lean_dec(v_a_1489_);
return v___x_1490_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_1480_ = stack[0].m_obj;
lean_object* v_fn_1481_ = stack[1].m_obj;
lean_object* v___y_1482_ = stack[2].m_obj;
lean_object* v___y_1483_ = stack[3].m_obj;
lean_object* v___y_1484_ = stack[4].m_obj;
lean_object* v___y_1485_ = stack[5].m_obj;
lean_object* v_res_1502_;
v_res_1502_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(v_input_1480_, v_fn_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
stack->m_obj
 = v_res_1502_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___boxed(lean_object* v_input_1503_, lean_object* v_fn_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(v_input_1503_, v_fn_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
return v_res_1510_;
}
}
lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0(lean_object* v_f_1511_, lean_object* v_e_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v___x_1518_; 
lean_inc(v___y_1516_);
lean_inc_ref(v___y_1515_);
lean_inc(v___y_1514_);
lean_inc_ref(v___y_1513_);
v___x_1518_ = lean_apply_6(v_f_1511_, v_e_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, lean_box(0));
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1527_; 
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1527_ == 0)
{
lean_object* v_unused_1528_; 
v_unused_1528_ = lean_ctor_get(v___x_1518_, 0);
lean_dec(v_unused_1528_);
v___x_1520_ = v___x_1518_;
v_isShared_1521_ = v_isSharedCheck_1527_;
goto v_resetjp_1519_;
}
else
{
lean_dec(v___x_1518_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1527_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
uint8_t v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1525_; 
v___x_1522_ = 1;
v___x_1523_ = lean_box(v___x_1522_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1523_);
v___x_1525_ = v___x_1520_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
v_a_1529_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1518_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1518_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1511_ = stack[0].m_obj;
lean_object* v_e_1512_ = stack[1].m_obj;
lean_object* v___y_1513_ = stack[2].m_obj;
lean_object* v___y_1514_ = stack[3].m_obj;
lean_object* v___y_1515_ = stack[4].m_obj;
lean_object* v___y_1516_ = stack[5].m_obj;
lean_object* v_res_1537_;
v_res_1537_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0(v_f_1511_, v_e_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
stack->m_obj
 = v_res_1537_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0___boxed(lean_object* v_f_1538_, lean_object* v_e_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0(v_f_1538_, v_e_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
return v_res_1545_;
}
}
lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(lean_object* v_e_1546_, lean_object* v_f_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___f_1553_; lean_object* v___x_1554_; 
v___f_1553_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1553_, 0, v_f_1547_);
v___x_1554_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(v_e_1546_, v___f_1553_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
return v___x_1554_;
}
}
LEAN_EXPORT void l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1546_ = stack[0].m_obj;
lean_object* v_f_1547_ = stack[1].m_obj;
lean_object* v___y_1548_ = stack[2].m_obj;
lean_object* v___y_1549_ = stack[3].m_obj;
lean_object* v___y_1550_ = stack[4].m_obj;
lean_object* v___y_1551_ = stack[5].m_obj;
lean_object* v_res_1555_;
v_res_1555_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(v_e_1546_, v_f_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
stack->m_obj
 = v_res_1555_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___boxed(lean_object* v_e_1556_, lean_object* v_f_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(v_e_1556_, v_f_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
return v_res_1563_;
}
}
lean_object* l_Lean_Meta_setMVarUserNamesAt(lean_object* v_e_1566_, lean_object* v_isTarget_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___f_1576_; lean_object* v___x_1577_; lean_object* v_a_1578_; lean_object* v___x_1579_; 
v___x_1573_ = lean_unsigned_to_nat(0u);
v___x_1574_ = ((lean_object*)(l_Lean_Meta_setMVarUserNamesAt___closed__0));
v___x_1575_ = lean_st_mk_ref(v___x_1574_);
lean_inc(v___x_1575_);
v___f_1576_ = lean_alloc_closure((void*)(l_Lean_Meta_setMVarUserNamesAt___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1576_, 0, v___x_1575_);
lean_closure_set(v___f_1576_, 1, v_isTarget_1567_);
lean_closure_set(v___f_1576_, 2, v___x_1573_);
v___x_1577_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(v_e_1566_, v_a_1569_);
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref(v___x_1577_);
v___x_1579_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(v_a_1578_, v___f_1576_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1587_; 
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1587_ == 0)
{
lean_object* v_unused_1588_; 
v_unused_1588_ = lean_ctor_get(v___x_1579_, 0);
lean_dec(v_unused_1588_);
v___x_1581_ = v___x_1579_;
v_isShared_1582_ = v_isSharedCheck_1587_;
goto v_resetjp_1580_;
}
else
{
lean_dec(v___x_1579_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1587_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1583_ = lean_st_ref_get(v___x_1575_);
lean_dec(v___x_1575_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v___x_1583_);
v___x_1585_ = v___x_1581_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec(v___x_1575_);
v_a_1589_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1579_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1579_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_setMVarUserNamesAt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1566_ = stack[0].m_obj;
lean_object* v_isTarget_1567_ = stack[1].m_obj;
lean_object* v_a_1568_ = stack[2].m_obj;
lean_object* v_a_1569_ = stack[3].m_obj;
lean_object* v_a_1570_ = stack[4].m_obj;
lean_object* v_a_1571_ = stack[5].m_obj;
lean_object* v_res_1597_;
v_res_1597_ = l_Lean_Meta_setMVarUserNamesAt(v_e_1566_, v_isTarget_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_);
stack->m_obj
 = v_res_1597_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___boxed(lean_object* v_e_1598_, lean_object* v_isTarget_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_Meta_setMVarUserNamesAt(v_e_1598_, v_isTarget_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
return v_res_1605_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2(lean_object* v_upperBound_1606_, lean_object* v___x_1607_, lean_object* v_val_1608_, lean_object* v_e_1609_, lean_object* v_isTarget_1610_, lean_object* v_inst_1611_, lean_object* v_R_1612_, lean_object* v_a_1613_, lean_object* v_b_1614_, lean_object* v_c_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(v_upperBound_1606_, v___x_1607_, v_val_1608_, v_e_1609_, v_isTarget_1610_, v_a_1613_, v_b_1614_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1621_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1606_ = stack[0].m_obj;
lean_object* v___x_1607_ = stack[1].m_obj;
lean_object* v_val_1608_ = stack[2].m_obj;
lean_object* v_e_1609_ = stack[3].m_obj;
lean_object* v_isTarget_1610_ = stack[4].m_obj;
lean_object* v_a_1613_ = stack[7].m_obj;
lean_object* v_b_1614_ = stack[8].m_obj;
lean_object* v___y_1616_ = stack[10].m_obj;
lean_object* v___y_1617_ = stack[11].m_obj;
lean_object* v___y_1618_ = stack[12].m_obj;
lean_object* v___y_1619_ = stack[13].m_obj;
lean_object* v_res_1622_;
v_res_1622_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2(v_upperBound_1606_, v___x_1607_, v_val_1608_, v_e_1609_, v_isTarget_1610_, lean_box(0), lean_box(0), v_a_1613_, v_b_1614_, lean_box(0), v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
stack->m_obj
 = v_res_1622_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___boxed(lean_object* v_upperBound_1623_, lean_object* v___x_1624_, lean_object* v_val_1625_, lean_object* v_e_1626_, lean_object* v_isTarget_1627_, lean_object* v_inst_1628_, lean_object* v_R_1629_, lean_object* v_a_1630_, lean_object* v_b_1631_, lean_object* v_c_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2(v_upperBound_1623_, v___x_1624_, v_val_1625_, v_e_1626_, v_isTarget_1627_, v_inst_1628_, v_R_1629_, v_a_1630_, v_b_1631_, v_c_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec_ref(v_isTarget_1627_);
lean_dec_ref(v_e_1626_);
lean_dec_ref(v___x_1624_);
lean_dec(v_upperBound_1623_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_1639_, lean_object* v_m_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_m_1640_, v_a_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___boxed(lean_object* v_00_u03b2_1643_, lean_object* v_m_1644_, lean_object* v_a_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7(v_00_u03b2_1643_, v_m_1644_, v_a_1645_);
lean_dec_ref(v_a_1645_);
lean_dec_ref(v_m_1644_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_1647_, lean_object* v_m_1648_, lean_object* v_a_1649_, lean_object* v_b_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(v_m_1648_, v_a_1649_, v_b_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_1652_, lean_object* v_a_1653_, lean_object* v_x_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(v_a_1653_, v_x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03b2_1656_, lean_object* v_a_1657_, lean_object* v_x_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8(v_00_u03b2_1656_, v_a_1657_, v_x_1658_);
lean_dec(v_x_1658_);
lean_dec_ref(v_a_1657_);
return v_res_1659_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_1660_, lean_object* v_a_1661_, lean_object* v_x_1662_){
_start:
{
uint8_t v___x_1663_; 
v___x_1663_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_a_1661_, v_x_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1661_ = stack[1].m_obj;
lean_object* v_x_1662_ = stack[2].m_obj;
uint8_t v_res_1664_;
v_res_1664_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10(lean_box(0), v_a_1661_, v_x_1662_);
stack->m_num = v_res_1664_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b2_1665_, lean_object* v_a_1666_, lean_object* v_x_1667_){
_start:
{
uint8_t v_res_1668_; lean_object* v_r_1669_; 
v_res_1668_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10(v_00_u03b2_1665_, v_a_1666_, v_x_1667_);
lean_dec(v_x_1667_);
lean_dec_ref(v_a_1666_);
v_r_1669_ = lean_box(v_res_1668_);
return v_r_1669_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11(lean_object* v_00_u03b2_1670_, lean_object* v_data_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11___redArg(v_data_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12(lean_object* v_00_u03b2_1673_, lean_object* v_a_1674_, lean_object* v_b_1675_, lean_object* v_x_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(v_a_1674_, v_b_1675_, v_x_1676_);
return v___x_1677_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16(lean_object* v_00_u03b1_1678_, lean_object* v_name_1679_, uint8_t v_bi_1680_, lean_object* v_type_1681_, lean_object* v_k_1682_, uint8_t v_kind_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_name_1679_, v_bi_1680_, v_type_1681_, v_k_1682_, v_kind_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
return v___x_1690_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1679_ = stack[1].m_obj;
uint8_t v_bi_1680_ = stack[2].m_num;
lean_object* v_type_1681_ = stack[3].m_obj;
lean_object* v_k_1682_ = stack[4].m_obj;
uint8_t v_kind_1683_ = stack[5].m_num;
lean_object* v___y_1684_ = stack[6].m_obj;
lean_object* v___y_1685_ = stack[7].m_obj;
lean_object* v___y_1686_ = stack[8].m_obj;
lean_object* v___y_1687_ = stack[9].m_obj;
lean_object* v___y_1688_ = stack[10].m_obj;
lean_object* v_res_1691_;
v_res_1691_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16(lean_box(0), v_name_1679_, v_bi_1680_, v_type_1681_, v_k_1682_, v_kind_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
stack->m_obj
 = v_res_1691_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1692_, lean_object* v_name_1693_, lean_object* v_bi_1694_, lean_object* v_type_1695_, lean_object* v_k_1696_, lean_object* v_kind_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
uint8_t v_bi_boxed_1704_; uint8_t v_kind_boxed_1705_; lean_object* v_res_1706_; 
v_bi_boxed_1704_ = lean_unbox(v_bi_1694_);
v_kind_boxed_1705_ = lean_unbox(v_kind_1697_);
v_res_1706_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16(v_00_u03b1_1692_, v_name_1693_, v_bi_boxed_1704_, v_type_1695_, v_k_1696_, v_kind_boxed_1705_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
return v_res_1706_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21(lean_object* v_00_u03b1_1707_, lean_object* v_name_1708_, lean_object* v_type_1709_, lean_object* v_val_1710_, lean_object* v_k_1711_, uint8_t v_nondep_1712_, uint8_t v_kind_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(v_name_1708_, v_type_1709_, v_val_1710_, v_k_1711_, v_nondep_1712_, v_kind_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
return v___x_1720_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1708_ = stack[1].m_obj;
lean_object* v_type_1709_ = stack[2].m_obj;
lean_object* v_val_1710_ = stack[3].m_obj;
lean_object* v_k_1711_ = stack[4].m_obj;
uint8_t v_nondep_1712_ = stack[5].m_num;
uint8_t v_kind_1713_ = stack[6].m_num;
lean_object* v___y_1714_ = stack[7].m_obj;
lean_object* v___y_1715_ = stack[8].m_obj;
lean_object* v___y_1716_ = stack[9].m_obj;
lean_object* v___y_1717_ = stack[10].m_obj;
lean_object* v___y_1718_ = stack[11].m_obj;
lean_object* v_res_1721_;
v_res_1721_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21(lean_box(0), v_name_1708_, v_type_1709_, v_val_1710_, v_k_1711_, v_nondep_1712_, v_kind_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
stack->m_obj
 = v_res_1721_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___boxed(lean_object* v_00_u03b1_1722_, lean_object* v_name_1723_, lean_object* v_type_1724_, lean_object* v_val_1725_, lean_object* v_k_1726_, lean_object* v_nondep_1727_, lean_object* v_kind_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
uint8_t v_nondep_boxed_1735_; uint8_t v_kind_boxed_1736_; lean_object* v_res_1737_; 
v_nondep_boxed_1735_ = lean_unbox(v_nondep_1727_);
v_kind_boxed_1736_ = lean_unbox(v_kind_1728_);
v_res_1737_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21(v_00_u03b1_1722_, v_name_1723_, v_type_1724_, v_val_1725_, v_k_1726_, v_nondep_boxed_1735_, v_kind_boxed_1736_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_1738_, lean_object* v_i_1739_, lean_object* v_source_1740_, lean_object* v_target_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12___redArg(v_i_1739_, v_source_1740_, v_target_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16(lean_object* v_00_u03b2_1743_, lean_object* v_x_1744_, lean_object* v_x_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16___redArg(v_x_1744_, v_x_1745_);
return v___x_1746_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(lean_object* v_as_1747_, size_t v_sz_1748_, size_t v_i_1749_, lean_object* v_b_1750_, lean_object* v___y_1751_){
_start:
{
uint8_t v___x_1753_; 
v___x_1753_ = lean_usize_dec_lt(v_i_1749_, v_sz_1748_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; 
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v_b_1750_);
return v___x_1754_;
}
else
{
lean_object* v___x_1755_; lean_object* v_a_1756_; lean_object* v___x_1757_; lean_object* v_mctx_1758_; lean_object* v_cache_1759_; lean_object* v_zetaDeltaFVarIds_1760_; lean_object* v_postponed_1761_; lean_object* v_diag_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1775_; 
v___x_1755_ = lean_box(0);
v_a_1756_ = lean_array_uget_borrowed(v_as_1747_, v_i_1749_);
v___x_1757_ = lean_st_ref_take(v___y_1751_);
v_mctx_1758_ = lean_ctor_get(v___x_1757_, 0);
v_cache_1759_ = lean_ctor_get(v___x_1757_, 1);
v_zetaDeltaFVarIds_1760_ = lean_ctor_get(v___x_1757_, 2);
v_postponed_1761_ = lean_ctor_get(v___x_1757_, 3);
v_diag_1762_ = lean_ctor_get(v___x_1757_, 4);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1764_ = v___x_1757_;
v_isShared_1765_ = v_isSharedCheck_1775_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_diag_1762_);
lean_inc(v_postponed_1761_);
lean_inc(v_zetaDeltaFVarIds_1760_);
lean_inc(v_cache_1759_);
lean_inc(v_mctx_1758_);
lean_dec(v___x_1757_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1775_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1766_ = lean_box(0);
lean_inc(v_a_1756_);
v___x_1767_ = l_Lean_MetavarContext_setMVarUserNameTemporarily(v_mctx_1758_, v_a_1756_, v___x_1766_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1767_);
v___x_1769_ = v___x_1764_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1767_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_cache_1759_);
lean_ctor_set(v_reuseFailAlloc_1774_, 2, v_zetaDeltaFVarIds_1760_);
lean_ctor_set(v_reuseFailAlloc_1774_, 3, v_postponed_1761_);
lean_ctor_set(v_reuseFailAlloc_1774_, 4, v_diag_1762_);
v___x_1769_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1770_; size_t v___x_1771_; size_t v___x_1772_; 
v___x_1770_ = lean_st_ref_put(v___y_1751_, v___x_1769_);
v___x_1771_ = ((size_t)1ULL);
v___x_1772_ = lean_usize_add(v_i_1749_, v___x_1771_);
v_i_1749_ = v___x_1772_;
v_b_1750_ = v___x_1755_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1747_ = stack[0].m_obj;
size_t v_sz_1748_ = stack[1].m_num;
size_t v_i_1749_ = stack[2].m_num;
lean_object* v_b_1750_ = stack[3].m_obj;
lean_object* v___y_1751_ = stack[4].m_obj;
lean_object* v_res_1776_;
v_res_1776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_as_1747_, v_sz_1748_, v_i_1749_, v_b_1750_, v___y_1751_);
stack->m_obj
 = v_res_1776_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg___boxed(lean_object* v_as_1777_, lean_object* v_sz_1778_, lean_object* v_i_1779_, lean_object* v_b_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
size_t v_sz_boxed_1783_; size_t v_i_boxed_1784_; lean_object* v_res_1785_; 
v_sz_boxed_1783_ = lean_unbox_usize(v_sz_1778_);
lean_dec(v_sz_1778_);
v_i_boxed_1784_ = lean_unbox_usize(v_i_1779_);
lean_dec(v_i_1779_);
v_res_1785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_as_1777_, v_sz_boxed_1783_, v_i_boxed_1784_, v_b_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v_as_1777_);
return v_res_1785_;
}
}
lean_object* l_Lean_Meta_resetMVarUserNames(lean_object* v_toReset_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_){
_start:
{
lean_object* v___x_1792_; size_t v_sz_1793_; size_t v___x_1794_; lean_object* v___x_1795_; 
v___x_1792_ = lean_box(0);
v_sz_1793_ = lean_array_size(v_toReset_1786_);
v___x_1794_ = ((size_t)0ULL);
v___x_1795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_toReset_1786_, v_sz_1793_, v___x_1794_, v___x_1792_, v_a_1788_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1802_ == 0)
{
lean_object* v_unused_1803_; 
v_unused_1803_ = lean_ctor_get(v___x_1795_, 0);
lean_dec(v_unused_1803_);
v___x_1797_ = v___x_1795_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_dec(v___x_1795_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1792_);
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1792_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
else
{
return v___x_1795_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_resetMVarUserNames_0interp(lean_interpreter_value* stack)
{
lean_object* v_toReset_1786_ = stack[0].m_obj;
lean_object* v_a_1787_ = stack[1].m_obj;
lean_object* v_a_1788_ = stack[2].m_obj;
lean_object* v_a_1789_ = stack[3].m_obj;
lean_object* v_a_1790_ = stack[4].m_obj;
lean_object* v_res_1804_;
v_res_1804_ = l_Lean_Meta_resetMVarUserNames(v_toReset_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_);
stack->m_obj
 = v_res_1804_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_resetMVarUserNames___boxed(lean_object* v_toReset_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_Meta_resetMVarUserNames(v_toReset_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
lean_dec(v_a_1809_);
lean_dec_ref(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec_ref(v_toReset_1805_);
return v_res_1811_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0(lean_object* v_as_1812_, size_t v_sz_1813_, size_t v_i_1814_, lean_object* v_b_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_as_1812_, v_sz_1813_, v_i_1814_, v_b_1815_, v___y_1817_);
return v___x_1821_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1812_ = stack[0].m_obj;
size_t v_sz_1813_ = stack[1].m_num;
size_t v_i_1814_ = stack[2].m_num;
lean_object* v_b_1815_ = stack[3].m_obj;
lean_object* v___y_1816_ = stack[4].m_obj;
lean_object* v___y_1817_ = stack[5].m_obj;
lean_object* v___y_1818_ = stack[6].m_obj;
lean_object* v___y_1819_ = stack[7].m_obj;
lean_object* v_res_1822_;
v_res_1822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0(v_as_1812_, v_sz_1813_, v_i_1814_, v_b_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
stack->m_obj
 = v_res_1822_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___boxed(lean_object* v_as_1823_, lean_object* v_sz_1824_, lean_object* v_i_1825_, lean_object* v_b_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
size_t v_sz_boxed_1832_; size_t v_i_boxed_1833_; lean_object* v_res_1834_; 
v_sz_boxed_1832_ = lean_unbox_usize(v_sz_1824_);
lean_dec(v_sz_1824_);
v_i_boxed_1833_ = lean_unbox_usize(v_i_1825_);
lean_dec(v_i_1825_);
v_res_1834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0(v_as_1823_, v_sz_boxed_1832_, v_i_boxed_1833_, v_b_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec_ref(v_as_1823_);
return v_res_1834_;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(lean_object* v_x_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
if (lean_obj_tag(v_x_1835_) == 2)
{
lean_object* v_mvarId_1841_; lean_object* v___x_1842_; 
v_mvarId_1841_ = lean_ctor_get(v_x_1835_, 0);
lean_inc(v_mvarId_1841_);
lean_dec_ref_known(v_x_1835_, 1);
v___x_1842_ = l_Lean_MVarId_getDecl(v_mvarId_1841_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1853_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1845_ = v___x_1842_;
v_isShared_1846_ = v_isSharedCheck_1853_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1853_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v_userName_1847_; uint8_t v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1851_; 
v_userName_1847_ = lean_ctor_get(v_a_1843_, 0);
lean_inc(v_userName_1847_);
lean_dec(v_a_1843_);
v___x_1848_ = l_Lean_Name_isAnonymous(v_userName_1847_);
lean_dec(v_userName_1847_);
v___x_1849_ = lean_box(v___x_1848_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v___x_1849_);
v___x_1851_ = v___x_1845_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
v_a_1854_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1842_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1842_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
else
{
uint8_t v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
lean_dec_ref(v_x_1835_);
v___x_1862_ = 0;
v___x_1863_ = lean_box(v___x_1862_);
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
return v___x_1864_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1835_ = stack[0].m_obj;
lean_object* v___y_1836_ = stack[1].m_obj;
lean_object* v___y_1837_ = stack[2].m_obj;
lean_object* v___y_1838_ = stack[3].m_obj;
lean_object* v___y_1839_ = stack[4].m_obj;
lean_object* v_res_1865_;
v_res_1865_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(v_x_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
stack->m_obj
 = v_res_1865_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0___boxed(lean_object* v_x_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(v_x_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
return v_res_1872_;
}
}
lean_object* l_Lean_Meta_mkForallFVars_x27___lam__0(lean_object* v_val_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_x3f_1878_){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_st_ref_get(v_val_1873_);
v___x_1881_ = l_Lean_Meta_resetMVarUserNames(v___x_1880_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_);
lean_dec(v___x_1880_);
return v___x_1881_;
}
}
LEAN_EXPORT void l_Lean_Meta_mkForallFVars_x27___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1873_ = stack[0].m_obj;
lean_object* v_a_1874_ = stack[1].m_obj;
lean_object* v_a_1875_ = stack[2].m_obj;
lean_object* v_a_1876_ = stack[3].m_obj;
lean_object* v_a_1877_ = stack[4].m_obj;
lean_object* v_a_x3f_1878_ = stack[5].m_obj;
lean_object* v_res_1882_;
v_res_1882_ = l_Lean_Meta_mkForallFVars_x27___lam__0(v_val_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_x3f_1878_);
stack->m_obj
 = v_res_1882_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__0___boxed(lean_object* v_val_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_x3f_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_Meta_mkForallFVars_x27___lam__0(v_val_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_x3f_1888_);
lean_dec(v_a_x3f_1888_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
lean_dec(v_val_1883_);
return v_res_1890_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(lean_object* v_xs_1891_, lean_object* v_as_1892_, size_t v_sz_1893_, size_t v_i_1894_, lean_object* v_b_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
uint8_t v___x_1902_; 
v___x_1902_ = lean_usize_dec_lt(v_i_1894_, v_sz_1893_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; 
lean_dec_ref(v_xs_1891_);
v___x_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1903_, 0, v_b_1895_);
return v___x_1903_;
}
else
{
lean_object* v___x_1904_; lean_object* v_a_1905_; lean_object* v___x_1906_; 
v___x_1904_ = lean_box(0);
v_a_1905_ = lean_array_uget_borrowed(v_as_1892_, v_i_1894_);
lean_inc(v___y_1900_);
lean_inc_ref(v___y_1899_);
lean_inc(v___y_1898_);
lean_inc_ref(v___y_1897_);
lean_inc(v_a_1905_);
v___x_1906_ = lean_infer_type(v_a_1905_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1908_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1906_, 1);
lean_inc_ref(v_xs_1891_);
v___x_1908_ = l_Lean_Meta_setMVarUserNamesAt(v_a_1907_, v_xs_1891_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; size_t v___x_1913_; size_t v___x_1914_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref_known(v___x_1908_, 1);
v___x_1910_ = lean_st_ref_take(v___y_1896_);
v___x_1911_ = l_Array_append___redArg(v___x_1910_, v_a_1909_);
lean_dec(v_a_1909_);
v___x_1912_ = lean_st_ref_put(v___y_1896_, v___x_1911_);
v___x_1913_ = ((size_t)1ULL);
v___x_1914_ = lean_usize_add(v_i_1894_, v___x_1913_);
v_i_1894_ = v___x_1914_;
v_b_1895_ = v___x_1904_;
goto _start;
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec_ref(v_xs_1891_);
v_a_1916_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1908_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1908_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
lean_dec_ref(v_xs_1891_);
v_a_1924_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1926_ = v___x_1906_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1906_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1924_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1891_ = stack[0].m_obj;
lean_object* v_as_1892_ = stack[1].m_obj;
size_t v_sz_1893_ = stack[2].m_num;
size_t v_i_1894_ = stack[3].m_num;
lean_object* v_b_1895_ = stack[4].m_obj;
lean_object* v___y_1896_ = stack[5].m_obj;
lean_object* v___y_1897_ = stack[6].m_obj;
lean_object* v___y_1898_ = stack[7].m_obj;
lean_object* v___y_1899_ = stack[8].m_obj;
lean_object* v___y_1900_ = stack[9].m_obj;
lean_object* v_res_1932_;
v_res_1932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(v_xs_1891_, v_as_1892_, v_sz_1893_, v_i_1894_, v_b_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
stack->m_obj
 = v_res_1932_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2___boxed(lean_object* v_xs_1933_, lean_object* v_as_1934_, lean_object* v_sz_1935_, lean_object* v_i_1936_, lean_object* v_b_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
size_t v_sz_boxed_1944_; size_t v_i_boxed_1945_; lean_object* v_res_1946_; 
v_sz_boxed_1944_ = lean_unbox_usize(v_sz_1935_);
lean_dec(v_sz_1935_);
v_i_boxed_1945_ = lean_unbox_usize(v_i_1936_);
lean_dec(v_i_1936_);
v_res_1946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(v_xs_1933_, v_as_1934_, v_sz_boxed_1944_, v_i_boxed_1945_, v_b_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v_as_1934_);
return v_res_1946_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(lean_object* v_xs_1947_, lean_object* v_as_1948_, size_t v_sz_1949_, size_t v_i_1950_, lean_object* v_b_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
uint8_t v___x_1958_; 
v___x_1958_ = lean_usize_dec_lt(v_i_1950_, v_sz_1949_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; 
lean_dec_ref(v_xs_1947_);
v___x_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1959_, 0, v_b_1951_);
return v___x_1959_;
}
else
{
lean_object* v___x_1960_; lean_object* v_a_1961_; lean_object* v___x_1962_; 
v___x_1960_ = lean_box(0);
v_a_1961_ = lean_array_uget_borrowed(v_as_1948_, v_i_1950_);
lean_inc(v___y_1956_);
lean_inc_ref(v___y_1955_);
lean_inc(v___y_1954_);
lean_inc_ref(v___y_1953_);
lean_inc(v_a_1961_);
v___x_1962_ = lean_infer_type(v_a_1961_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1964_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1962_, 1);
lean_inc_ref(v_xs_1947_);
v___x_1964_ = l_Lean_Meta_setMVarUserNamesAt(v_a_1963_, v_xs_1947_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; size_t v___x_1969_; size_t v___x_1970_; lean_object* v___x_1971_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v___x_1964_, 1);
v___x_1966_ = lean_st_ref_take(v___y_1952_);
v___x_1967_ = l_Array_append___redArg(v___x_1966_, v_a_1965_);
lean_dec(v_a_1965_);
v___x_1968_ = lean_st_ref_put(v___y_1952_, v___x_1967_);
v___x_1969_ = ((size_t)1ULL);
v___x_1970_ = lean_usize_add(v_i_1950_, v___x_1969_);
v___x_1971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(v_xs_1947_, v_as_1948_, v_sz_1949_, v___x_1970_, v___x_1960_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
return v___x_1971_;
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec_ref(v_xs_1947_);
v_a_1972_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1964_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1964_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref(v_xs_1947_);
v_a_1980_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1962_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1962_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1947_ = stack[0].m_obj;
lean_object* v_as_1948_ = stack[1].m_obj;
size_t v_sz_1949_ = stack[2].m_num;
size_t v_i_1950_ = stack[3].m_num;
lean_object* v_b_1951_ = stack[4].m_obj;
lean_object* v___y_1952_ = stack[5].m_obj;
lean_object* v___y_1953_ = stack[6].m_obj;
lean_object* v___y_1954_ = stack[7].m_obj;
lean_object* v___y_1955_ = stack[8].m_obj;
lean_object* v___y_1956_ = stack[9].m_obj;
lean_object* v_res_1988_;
v_res_1988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(v_xs_1947_, v_as_1948_, v_sz_1949_, v_i_1950_, v_b_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
stack->m_obj
 = v_res_1988_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2___boxed(lean_object* v_xs_1989_, lean_object* v_as_1990_, lean_object* v_sz_1991_, lean_object* v_i_1992_, lean_object* v_b_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
size_t v_sz_boxed_2000_; size_t v_i_boxed_2001_; lean_object* v_res_2002_; 
v_sz_boxed_2000_ = lean_unbox_usize(v_sz_1991_);
lean_dec(v_sz_1991_);
v_i_boxed_2001_ = lean_unbox_usize(v_i_1992_);
lean_dec(v_i_1992_);
v_res_2002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(v_xs_1989_, v_as_1990_, v_sz_boxed_2000_, v_i_boxed_2001_, v_b_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v_as_1990_);
return v_res_2002_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(lean_object* v_as_2003_, size_t v_i_2004_, size_t v_stop_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
uint8_t v___x_2011_; 
v___x_2011_ = lean_usize_dec_eq(v_i_2004_, v_stop_2005_);
if (v___x_2011_ == 0)
{
uint8_t v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2012_ = 1;
v___x_2013_ = lean_array_uget_borrowed(v_as_2003_, v_i_2004_);
lean_inc(v___x_2013_);
v___x_2014_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(v___x_2013_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2027_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2027_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2027_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
uint8_t v___x_2019_; 
v___x_2019_ = lean_unbox(v_a_2015_);
lean_dec(v_a_2015_);
if (v___x_2019_ == 0)
{
size_t v___x_2020_; size_t v___x_2021_; 
lean_del_object(v___x_2017_);
v___x_2020_ = ((size_t)1ULL);
v___x_2021_ = lean_usize_add(v_i_2004_, v___x_2020_);
v_i_2004_ = v___x_2021_;
goto _start;
}
else
{
lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2023_ = lean_box(v___x_2012_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2023_);
v___x_2025_ = v___x_2017_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
else
{
return v___x_2014_;
}
}
else
{
uint8_t v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2028_ = 0;
v___x_2029_ = lean_box(v___x_2028_);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
return v___x_2030_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2003_ = stack[0].m_obj;
size_t v_i_2004_ = stack[1].m_num;
size_t v_stop_2005_ = stack[2].m_num;
lean_object* v___y_2006_ = stack[3].m_obj;
lean_object* v___y_2007_ = stack[4].m_obj;
lean_object* v___y_2008_ = stack[5].m_obj;
lean_object* v___y_2009_ = stack[6].m_obj;
lean_object* v_res_2031_;
v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(v_as_2003_, v_i_2004_, v_stop_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
stack->m_obj
 = v_res_2031_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1___boxed(lean_object* v_as_2032_, lean_object* v_i_2033_, lean_object* v_stop_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
size_t v_i_boxed_2040_; size_t v_stop_boxed_2041_; lean_object* v_res_2042_; 
v_i_boxed_2040_ = lean_unbox_usize(v_i_2033_);
lean_dec(v_i_2033_);
v_stop_boxed_2041_ = lean_unbox_usize(v_stop_2034_);
lean_dec(v_stop_2034_);
v_res_2042_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(v_as_2032_, v_i_boxed_2040_, v_stop_boxed_2041_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec_ref(v_as_2032_);
return v_res_2042_;
}
}
lean_object* l_Lean_Meta_mkForallFVars_x27(lean_object* v_xs_2043_, lean_object* v_type_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
uint8_t v_a_2051_; lean_object* v___x_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; 
v___x_2055_ = lean_unsigned_to_nat(0u);
v___x_2056_ = lean_array_get_size(v_xs_2043_);
v___x_2057_ = lean_nat_dec_lt(v___x_2055_, v___x_2056_);
if (v___x_2057_ == 0)
{
v_a_2051_ = v___x_2057_;
goto v___jp_2050_;
}
else
{
if (v___x_2057_ == 0)
{
v_a_2051_ = v___x_2057_;
goto v___jp_2050_;
}
else
{
size_t v___x_2058_; size_t v___x_2059_; lean_object* v___x_2060_; 
v___x_2058_ = ((size_t)0ULL);
v___x_2059_ = lean_usize_of_nat(v___x_2056_);
v___x_2060_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(v_xs_2043_, v___x_2058_, v___x_2059_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; uint8_t v___x_2062_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2060_, 1);
v___x_2062_ = lean_unbox(v_a_2061_);
if (v___x_2062_ == 0)
{
uint8_t v___x_2063_; 
v___x_2063_ = lean_unbox(v_a_2061_);
lean_dec(v_a_2061_);
v_a_2051_ = v___x_2063_;
goto v___jp_2050_;
}
else
{
lean_object* v___x_2064_; size_t v_sz_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v_a_2069_; lean_object* v___x_2088_; 
lean_dec(v_a_2061_);
v___x_2064_ = lean_box(0);
v_sz_2065_ = lean_array_size(v_xs_2043_);
v___x_2066_ = ((lean_object*)(l_Lean_Meta_setMVarUserNamesAt___closed__0));
v___x_2067_ = lean_st_mk_ref(v___x_2066_);
lean_inc_ref(v_xs_2043_);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(v_xs_2043_, v_xs_2043_, v_sz_2065_, v___x_2058_, v___x_2064_, v___x_2067_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v___x_2089_; 
lean_dec_ref_known(v___x_2088_, 1);
lean_inc_ref(v_xs_2043_);
lean_inc_ref(v_type_2044_);
v___x_2089_ = l_Lean_Meta_setMVarUserNamesAt(v_type_2044_, v_xs_2043_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; uint8_t v___x_2095_; lean_object* v___x_2096_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2089_, 1);
v___x_2091_ = lean_st_ref_take(v___x_2067_);
v___x_2092_ = l_Array_append___redArg(v___x_2091_, v_a_2090_);
lean_dec(v_a_2090_);
v___x_2093_ = lean_st_ref_put(v___x_2067_, v___x_2092_);
v___x_2094_ = 0;
v___x_2095_ = 1;
v___x_2096_ = l_Lean_Meta_mkForallFVars(v_xs_2043_, v_type_2044_, v___x_2094_, v___x_2057_, v___x_2057_, v___x_2095_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
lean_dec_ref(v_xs_2043_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2122_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2122_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2122_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
lean_inc(v_a_2097_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set_tag(v___x_2099_, 1);
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Lean_Meta_mkForallFVars_x27___lam__0(v___x_2067_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v___x_2102_);
lean_dec_ref(v___x_2102_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2111_; 
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2111_ == 0)
{
lean_object* v_unused_2112_; 
v_unused_2112_ = lean_ctor_get(v___x_2103_, 0);
lean_dec(v_unused_2112_);
v___x_2105_ = v___x_2103_;
v_isShared_2106_ = v_isSharedCheck_2111_;
goto v_resetjp_2104_;
}
else
{
lean_dec(v___x_2103_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2111_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2107_ = lean_st_ref_get(v___x_2067_);
lean_dec(v___x_2067_);
lean_dec(v___x_2107_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v_a_2097_);
v___x_2109_ = v___x_2105_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2097_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec(v_a_2097_);
lean_dec(v___x_2067_);
v_a_2113_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2103_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2103_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
}
}
else
{
lean_object* v_a_2123_; 
v_a_2123_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2096_, 1);
v_a_2069_ = v_a_2123_;
goto v___jp_2068_;
}
}
else
{
lean_object* v_a_2124_; 
lean_dec_ref(v_type_2044_);
lean_dec_ref(v_xs_2043_);
v_a_2124_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2089_, 1);
v_a_2069_ = v_a_2124_;
goto v___jp_2068_;
}
}
else
{
lean_object* v_a_2125_; 
lean_dec_ref(v_type_2044_);
lean_dec_ref(v_xs_2043_);
v_a_2125_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2088_, 1);
v_a_2069_ = v_a_2125_;
goto v___jp_2068_;
}
v___jp_2068_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = lean_box(0);
v___x_2071_ = l_Lean_Meta_mkForallFVars_x27___lam__0(v___x_2067_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v___x_2070_);
lean_dec(v___x_2067_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2078_ == 0)
{
lean_object* v_unused_2079_; 
v_unused_2079_ = lean_ctor_get(v___x_2071_, 0);
lean_dec(v_unused_2079_);
v___x_2073_ = v___x_2071_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_dec(v___x_2071_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
lean_ctor_set_tag(v___x_2073_, 1);
lean_ctor_set(v___x_2073_, 0, v_a_2069_);
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2069_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec_ref(v_a_2069_);
v_a_2080_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2071_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2071_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_dec_ref(v_type_2044_);
lean_dec_ref(v_xs_2043_);
v_a_2126_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2060_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2060_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
}
v___jp_2050_:
{
uint8_t v___x_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; 
v___x_2052_ = 1;
v___x_2053_ = 1;
v___x_2054_ = l_Lean_Meta_mkForallFVars(v_xs_2043_, v_type_2044_, v_a_2051_, v___x_2052_, v___x_2052_, v___x_2053_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
lean_dec_ref(v_xs_2043_);
return v___x_2054_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_mkForallFVars_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2043_ = stack[0].m_obj;
lean_object* v_type_2044_ = stack[1].m_obj;
lean_object* v_a_2045_ = stack[2].m_obj;
lean_object* v_a_2046_ = stack[3].m_obj;
lean_object* v_a_2047_ = stack[4].m_obj;
lean_object* v_a_2048_ = stack[5].m_obj;
lean_object* v_res_2134_;
v_res_2134_ = l_Lean_Meta_mkForallFVars_x27(v_xs_2043_, v_type_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_);
stack->m_obj
 = v_res_2134_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___boxed(lean_object* v_xs_2135_, lean_object* v_type_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_Meta_mkForallFVars_x27(v_xs_2135_, v_type_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
return v_res_2142_;
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
