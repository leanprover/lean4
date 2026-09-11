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
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v_nbuckets_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1145_ = lean_array_get_size(v_data_1144_);
v___x_1146_ = lean_unsigned_to_nat(2u);
v_nbuckets_1147_ = lean_nat_mul(v___x_1145_, v___x_1146_);
v___x_1148_ = lean_unsigned_to_nat(0u);
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_mk_array(v_nbuckets_1147_, v___x_1149_);
v___x_1151_ = lean_array_propagate_mark(v_data_1144_, v___x_1150_);
v___x_1152_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12___redArg(v___x_1148_, v_data_1144_, v___x_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(lean_object* v_a_1153_, lean_object* v_x_1154_){
_start:
{
if (lean_obj_tag(v_x_1154_) == 0)
{
uint8_t v___x_1155_; 
v___x_1155_ = 0;
return v___x_1155_;
}
else
{
lean_object* v_key_1156_; lean_object* v_tail_1157_; uint8_t v___x_1158_; 
v_key_1156_ = lean_ctor_get(v_x_1154_, 0);
v_tail_1157_ = lean_ctor_get(v_x_1154_, 2);
v___x_1158_ = lean_expr_eqv(v_key_1156_, v_a_1153_);
if (v___x_1158_ == 0)
{
v_x_1154_ = v_tail_1157_;
goto _start;
}
else
{
return v___x_1158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_a_1160_, lean_object* v_x_1161_){
_start:
{
uint8_t v_res_1162_; lean_object* v_r_1163_; 
v_res_1162_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_a_1160_, v_x_1161_);
lean_dec(v_x_1161_);
lean_dec_ref(v_a_1160_);
v_r_1163_ = lean_box(v_res_1162_);
return v_r_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(lean_object* v_m_1164_, lean_object* v_a_1165_, lean_object* v_b_1166_){
_start:
{
lean_object* v_size_1167_; lean_object* v_buckets_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1211_; 
v_size_1167_ = lean_ctor_get(v_m_1164_, 0);
v_buckets_1168_ = lean_ctor_get(v_m_1164_, 1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_m_1164_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1170_ = v_m_1164_;
v_isShared_1171_ = v_isSharedCheck_1211_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_buckets_1168_);
lean_inc(v_size_1167_);
lean_dec(v_m_1164_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1211_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; uint64_t v___x_1173_; uint64_t v___x_1174_; uint64_t v___x_1175_; uint64_t v_fold_1176_; uint64_t v___x_1177_; uint64_t v___x_1178_; uint64_t v___x_1179_; size_t v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; size_t v___x_1183_; size_t v___x_1184_; lean_object* v_bkt_1185_; uint8_t v___x_1186_; 
v___x_1172_ = lean_array_get_size(v_buckets_1168_);
v___x_1173_ = l_Lean_Expr_hash(v_a_1165_);
v___x_1174_ = 32ULL;
v___x_1175_ = lean_uint64_shift_right(v___x_1173_, v___x_1174_);
v_fold_1176_ = lean_uint64_xor(v___x_1173_, v___x_1175_);
v___x_1177_ = 16ULL;
v___x_1178_ = lean_uint64_shift_right(v_fold_1176_, v___x_1177_);
v___x_1179_ = lean_uint64_xor(v_fold_1176_, v___x_1178_);
v___x_1180_ = lean_uint64_to_usize(v___x_1179_);
v___x_1181_ = lean_usize_of_nat(v___x_1172_);
v___x_1182_ = ((size_t)1ULL);
v___x_1183_ = lean_usize_sub(v___x_1181_, v___x_1182_);
v___x_1184_ = lean_usize_land(v___x_1180_, v___x_1183_);
v_bkt_1185_ = lean_array_uget_borrowed(v_buckets_1168_, v___x_1184_);
v___x_1186_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_a_1165_, v_bkt_1185_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v_size_x27_1188_; lean_object* v___x_1189_; lean_object* v_buckets_x27_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1187_ = lean_unsigned_to_nat(1u);
v_size_x27_1188_ = lean_nat_add(v_size_1167_, v___x_1187_);
lean_dec(v_size_1167_);
lean_inc(v_bkt_1185_);
v___x_1189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1189_, 0, v_a_1165_);
lean_ctor_set(v___x_1189_, 1, v_b_1166_);
lean_ctor_set(v___x_1189_, 2, v_bkt_1185_);
v_buckets_x27_1190_ = lean_array_uset(v_buckets_1168_, v___x_1184_, v___x_1189_);
v___x_1191_ = lean_unsigned_to_nat(4u);
v___x_1192_ = lean_nat_mul(v_size_x27_1188_, v___x_1191_);
v___x_1193_ = lean_unsigned_to_nat(3u);
v___x_1194_ = lean_nat_div(v___x_1192_, v___x_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_array_get_size(v_buckets_x27_1190_);
v___x_1196_ = lean_nat_dec_le(v___x_1194_, v___x_1195_);
lean_dec(v___x_1194_);
if (v___x_1196_ == 0)
{
lean_object* v_val_1197_; lean_object* v___x_1199_; 
v_val_1197_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11___redArg(v_buckets_x27_1190_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v_val_1197_);
lean_ctor_set(v___x_1170_, 0, v_size_x27_1188_);
v___x_1199_ = v___x_1170_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_size_x27_1188_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_val_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
else
{
lean_object* v___x_1202_; 
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v_buckets_x27_1190_);
lean_ctor_set(v___x_1170_, 0, v_size_x27_1188_);
v___x_1202_ = v___x_1170_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_size_x27_1188_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_buckets_x27_1190_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
else
{
lean_object* v___x_1204_; lean_object* v_buckets_x27_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
lean_inc(v_bkt_1185_);
v___x_1204_ = lean_box(0);
v_buckets_x27_1205_ = lean_array_uset(v_buckets_1168_, v___x_1184_, v___x_1204_);
v___x_1206_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(v_a_1165_, v_b_1166_, v_bkt_1185_);
v___x_1207_ = lean_array_uset(v_buckets_x27_1205_, v___x_1184_, v___x_1206_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v___x_1207_);
v___x_1209_ = v___x_1170_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_size_1167_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1(lean_object* v_a_1212_, lean_object* v_e_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1216_ = lean_st_ref_take(v_a_1212_);
v___x_1217_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(v___x_1216_, v_e_1213_, v_a_1214_);
v___x_1218_ = lean_st_ref_put(v_a_1212_, v___x_1217_);
v___x_1219_ = lean_box(0);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_a_1220_, lean_object* v_e_1221_, lean_object* v_a_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1(v_a_1220_, v_e_1221_, v_a_1222_);
lean_dec(v_a_1220_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(lean_object* v_name_1225_, lean_object* v_type_1226_, lean_object* v_val_1227_, lean_object* v_k_1228_, uint8_t v_nondep_1229_, uint8_t v_kind_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___f_1237_; lean_object* v___x_1238_; 
lean_inc(v___y_1231_);
v___f_1237_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1237_, 0, v_k_1228_);
lean_closure_set(v___f_1237_, 1, v___y_1231_);
v___x_1238_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1225_, v_type_1226_, v_val_1227_, v___f_1237_, v_nondep_1229_, v_kind_1230_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
if (lean_obj_tag(v___x_1238_) == 0)
{
return v___x_1238_;
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg___boxed(lean_object* v_name_1247_, lean_object* v_type_1248_, lean_object* v_val_1249_, lean_object* v_k_1250_, lean_object* v_nondep_1251_, lean_object* v_kind_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
uint8_t v_nondep_boxed_1259_; uint8_t v_kind_boxed_1260_; lean_object* v_res_1261_; 
v_nondep_boxed_1259_ = lean_unbox(v_nondep_1251_);
v_kind_boxed_1260_ = lean_unbox(v_kind_1252_);
v_res_1261_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(v_name_1247_, v_type_1248_, v_val_1249_, v_k_1250_, v_nondep_boxed_1259_, v_kind_boxed_1260_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0___boxed(lean_object* v_fvars_1262_, lean_object* v_f_1263_, lean_object* v_body_1264_, lean_object* v_x_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0(v_fvars_1262_, v_f_1263_, v_body_1264_, v_x_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(lean_object* v_f_1273_, lean_object* v_fvars_1274_, lean_object* v_a_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
if (lean_obj_tag(v_a_1275_) == 8)
{
lean_object* v_declName_1282_; lean_object* v_type_1283_; lean_object* v_value_1284_; lean_object* v_body_1285_; lean_object* v_d_1286_; lean_object* v___x_1287_; 
v_declName_1282_ = lean_ctor_get(v_a_1275_, 0);
lean_inc(v_declName_1282_);
v_type_1283_ = lean_ctor_get(v_a_1275_, 1);
lean_inc_ref(v_type_1283_);
v_value_1284_ = lean_ctor_get(v_a_1275_, 2);
lean_inc_ref(v_value_1284_);
v_body_1285_ = lean_ctor_get(v_a_1275_, 3);
lean_inc_ref(v_body_1285_);
lean_dec_ref_known(v_a_1275_, 4);
v_d_1286_ = lean_expr_instantiate_rev(v_type_1283_, v_fvars_1274_);
lean_dec_ref(v_type_1283_);
lean_inc_ref(v_f_1273_);
lean_inc(v___y_1280_);
lean_inc_ref(v___y_1279_);
lean_inc(v___y_1278_);
lean_inc_ref(v___y_1277_);
lean_inc(v___y_1276_);
lean_inc_ref(v_d_1286_);
v___x_1287_ = lean_apply_7(v_f_1273_, v_d_1286_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, lean_box(0));
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_v_1288_; lean_object* v___x_1289_; 
lean_dec_ref_known(v___x_1287_, 1);
v_v_1288_ = lean_expr_instantiate_rev(v_value_1284_, v_fvars_1274_);
lean_dec_ref(v_value_1284_);
lean_inc_ref(v_f_1273_);
lean_inc(v___y_1280_);
lean_inc_ref(v___y_1279_);
lean_inc(v___y_1278_);
lean_inc_ref(v___y_1277_);
lean_inc(v___y_1276_);
lean_inc_ref(v_v_1288_);
v___x_1289_ = lean_apply_7(v_f_1273_, v_v_1288_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, lean_box(0));
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v___f_1290_; uint8_t v___x_1291_; uint8_t v___x_1292_; lean_object* v___x_1293_; 
lean_dec_ref_known(v___x_1289_, 1);
v___f_1290_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1290_, 0, v_fvars_1274_);
lean_closure_set(v___f_1290_, 1, v_f_1273_);
lean_closure_set(v___f_1290_, 2, v_body_1285_);
v___x_1291_ = 0;
v___x_1292_ = 0;
v___x_1293_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(v_declName_1282_, v_d_1286_, v_v_1288_, v___f_1290_, v___x_1291_, v___x_1292_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1293_;
}
else
{
lean_dec_ref(v_v_1288_);
lean_dec_ref(v_d_1286_);
lean_dec_ref(v_body_1285_);
lean_dec(v_declName_1282_);
lean_dec_ref(v_fvars_1274_);
lean_dec_ref(v_f_1273_);
return v___x_1289_;
}
}
else
{
lean_dec_ref(v_d_1286_);
lean_dec_ref(v_body_1285_);
lean_dec_ref(v_value_1284_);
lean_dec(v_declName_1282_);
lean_dec_ref(v_fvars_1274_);
lean_dec_ref(v_f_1273_);
return v___x_1287_;
}
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_expr_instantiate_rev(v_a_1275_, v_fvars_1274_);
lean_dec_ref(v_fvars_1274_);
lean_dec_ref(v_a_1275_);
lean_inc(v___y_1280_);
lean_inc_ref(v___y_1279_);
lean_inc(v___y_1278_);
lean_inc_ref(v___y_1277_);
lean_inc(v___y_1276_);
v___x_1295_ = lean_apply_7(v_f_1273_, v___x_1294_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, lean_box(0));
return v___x_1295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___lam__0(lean_object* v_fvars_1296_, lean_object* v_f_1297_, lean_object* v_body_1298_, lean_object* v_x_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_array_push(v_fvars_1296_, v_x_1299_);
v___x_1307_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(v_f_1297_, v___x_1306_, v_body_1298_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18___boxed(lean_object* v_f_1308_, lean_object* v_fvars_1309_, lean_object* v_a_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(v_f_1308_, v_fvars_1309_, v_a_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(lean_object* v_f_1318_, lean_object* v_e_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = ((lean_object*)(l_Lean_Meta_visitLambda___redArg___closed__0));
v___x_1327_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18(v_f_1318_, v___x_1326_, v_e_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11___boxed(lean_object* v_f_1328_, lean_object* v_e_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(v_f_1328_, v_e_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed(lean_object* v_fn_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2(v_fn_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(lean_object* v_fn_1346_, lean_object* v_e_1347_, lean_object* v_a_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v_a_1355_; lean_object* v___y_1367_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
lean_inc(v_a_1348_);
v___x_1369_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1369_, 0, lean_box(0));
lean_closure_set(v___x_1369_, 1, lean_box(0));
lean_closure_set(v___x_1369_, 2, v_a_1348_);
v___x_1370_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_box(0), v___x_1369_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1407_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1373_ = v___x_1370_;
v_isShared_1374_ = v_isSharedCheck_1407_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1407_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_a_1371_, v_e_1347_);
lean_dec(v_a_1371_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v___x_1376_; 
lean_del_object(v___x_1373_);
lean_inc_ref(v_fn_1346_);
lean_inc(v___y_1352_);
lean_inc_ref(v___y_1351_);
lean_inc(v___y_1350_);
lean_inc_ref(v___y_1349_);
lean_inc_ref(v_e_1347_);
v___x_1376_ = lean_apply_6(v_fn_1346_, v_e_1347_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, lean_box(0));
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; uint8_t v___x_1378_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
v___x_1378_ = lean_unbox(v_a_1377_);
lean_dec(v_a_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; 
lean_dec_ref(v_fn_1346_);
v___x_1379_ = lean_box(0);
v_a_1355_ = v___x_1379_;
goto v___jp_1354_;
}
else
{
switch(lean_obj_tag(v_e_1347_))
{
case 7:
{
lean_object* v___f_1380_; lean_object* v___x_1381_; 
v___f_1380_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1380_, 0, v_fn_1346_);
lean_inc_ref(v_e_1347_);
v___x_1381_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9(v___f_1380_, v_e_1347_, v_a_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
v___y_1367_ = v___x_1381_;
goto v___jp_1366_;
}
case 6:
{
lean_object* v___f_1382_; lean_object* v___x_1383_; 
v___f_1382_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1382_, 0, v_fn_1346_);
lean_inc_ref(v_e_1347_);
v___x_1383_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__10(v___f_1382_, v_e_1347_, v_a_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
v___y_1367_ = v___x_1383_;
goto v___jp_1366_;
}
case 8:
{
lean_object* v___f_1384_; lean_object* v___x_1385_; 
v___f_1384_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2___boxed), 8, 1);
lean_closure_set(v___f_1384_, 0, v_fn_1346_);
lean_inc_ref(v_e_1347_);
v___x_1385_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11(v___f_1384_, v_e_1347_, v_a_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
v___y_1367_ = v___x_1385_;
goto v___jp_1366_;
}
case 5:
{
lean_object* v_fn_1386_; lean_object* v_arg_1387_; lean_object* v___x_1388_; 
v_fn_1386_ = lean_ctor_get(v_e_1347_, 0);
v_arg_1387_ = lean_ctor_get(v_e_1347_, 1);
lean_inc_ref(v_fn_1386_);
lean_inc_ref(v_fn_1346_);
v___x_1388_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1346_, v_fn_1386_, v_a_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v___x_1389_; 
lean_dec_ref_known(v___x_1388_, 1);
lean_inc_ref(v_arg_1387_);
v___x_1389_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1346_, v_arg_1387_, v_a_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
v___y_1367_ = v___x_1389_;
goto v___jp_1366_;
}
else
{
lean_dec_ref(v_fn_1346_);
v___y_1367_ = v___x_1388_;
goto v___jp_1366_;
}
}
case 10:
{
lean_object* v_expr_1390_; lean_object* v___x_1391_; 
v_expr_1390_ = lean_ctor_get(v_e_1347_, 1);
lean_inc_ref(v_expr_1390_);
v___x_1391_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1346_, v_expr_1390_, v_a_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
v___y_1367_ = v___x_1391_;
goto v___jp_1366_;
}
case 11:
{
lean_object* v_struct_1392_; lean_object* v___x_1393_; 
v_struct_1392_ = lean_ctor_get(v_e_1347_, 2);
lean_inc_ref(v_struct_1392_);
v___x_1393_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1346_, v_struct_1392_, v_a_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
v___y_1367_ = v___x_1393_;
goto v___jp_1366_;
}
default: 
{
lean_object* v___x_1394_; 
lean_dec_ref(v_fn_1346_);
v___x_1394_ = lean_box(0);
v_a_1355_ = v___x_1394_;
goto v___jp_1354_;
}
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_dec_ref(v_e_1347_);
lean_dec_ref(v_fn_1346_);
v_a_1395_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1376_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1376_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
else
{
lean_object* v_val_1403_; lean_object* v___x_1405_; 
lean_dec_ref(v_e_1347_);
lean_dec_ref(v_fn_1346_);
v_val_1403_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_val_1403_);
lean_dec_ref_known(v___x_1375_, 1);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v_val_1403_);
v___x_1405_ = v___x_1373_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_val_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec_ref(v_e_1347_);
lean_dec_ref(v_fn_1346_);
v_a_1408_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1370_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1370_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
v___jp_1354_:
{
lean_object* v___f_1356_; lean_object* v___x_1357_; 
lean_inc(v_a_1348_);
v___f_1356_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1356_, 0, v_a_1348_);
lean_closure_set(v___f_1356_, 1, v_e_1347_);
lean_closure_set(v___f_1356_, 2, v_a_1355_);
v___x_1357_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__0(lean_box(0), v___f_1356_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; 
v_unused_1365_ = lean_ctor_get(v___x_1357_, 0);
lean_dec(v_unused_1365_);
v___x_1359_ = v___x_1357_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_dec(v___x_1357_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v_a_1355_);
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1355_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
else
{
return v___x_1357_;
}
}
v___jp_1366_:
{
if (lean_obj_tag(v___y_1367_) == 0)
{
lean_object* v_a_1368_; 
v_a_1368_ = lean_ctor_get(v___y_1367_, 0);
lean_inc(v_a_1368_);
lean_dec_ref_known(v___y_1367_, 1);
v_a_1355_ = v_a_1368_;
goto v___jp_1354_;
}
else
{
lean_dec_ref(v_e_1347_);
return v___y_1367_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___lam__2(lean_object* v_fn_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6___boxed(lean_object* v_fn_1425_, lean_object* v_e_1426_, lean_object* v_a_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1425_, v_e_1426_, v_a_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v_a_1427_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_object* v_00_u03b1_1434_, lean_object* v_x_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = lean_apply_1(v_x_1435_, lean_box(0));
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0___boxed(lean_object* v_00_u03b1_1443_, lean_object* v_x_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(v_00_u03b1_1443_, v_x_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(lean_object* v_input_1451_, lean_object* v_fn_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v_a_1460_; lean_object* v___x_1461_; 
v___x_1458_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___redArg___closed__2, &l_Lean_Meta_forEachExpr_x27___redArg___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__2);
v___x_1459_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_box(0), v___x_1458_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref(v___x_1459_);
v___x_1461_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6(v_fn_1452_, v_input_1451_, v_a_1460_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1461_, 1);
v___x_1463_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1463_, 0, lean_box(0));
lean_closure_set(v___x_1463_, 1, lean_box(0));
lean_closure_set(v___x_1463_, 2, v_a_1460_);
v___x_1464_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___lam__0(lean_box(0), v___x_1463_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1471_ == 0)
{
lean_object* v_unused_1472_; 
v_unused_1472_ = lean_ctor_get(v___x_1464_, 0);
lean_dec(v_unused_1472_);
v___x_1466_ = v___x_1464_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_dec(v___x_1464_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v_a_1462_);
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1462_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
else
{
lean_dec(v_a_1460_);
return v___x_1461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5___boxed(lean_object* v_input_1473_, lean_object* v_fn_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(v_input_1473_, v_fn_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0(lean_object* v_f_1481_, lean_object* v_e_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v___x_1488_; 
lean_inc(v___y_1486_);
lean_inc_ref(v___y_1485_);
lean_inc(v___y_1484_);
lean_inc_ref(v___y_1483_);
v___x_1488_ = lean_apply_6(v_f_1481_, v_e_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, lean_box(0));
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1497_; 
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; 
v_unused_1498_ = lean_ctor_get(v___x_1488_, 0);
lean_dec(v_unused_1498_);
v___x_1490_ = v___x_1488_;
v_isShared_1491_ = v_isSharedCheck_1497_;
goto v_resetjp_1489_;
}
else
{
lean_dec(v___x_1488_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1497_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
uint8_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1492_ = 1;
v___x_1493_ = lean_box(v___x_1492_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v___x_1493_);
v___x_1495_ = v___x_1490_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
v_a_1499_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1488_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1488_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0___boxed(lean_object* v_f_1507_, lean_object* v_e_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0(v_f_1507_, v_e_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(lean_object* v_e_1515_, lean_object* v_f_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___f_1522_; lean_object* v___x_1523_; 
v___f_1522_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1522_, 0, v_f_1516_);
v___x_1523_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5(v_e_1515_, v___f_1522_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4___boxed(lean_object* v_e_1524_, lean_object* v_f_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(v_e_1524_, v_f_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt(lean_object* v_e_1534_, lean_object* v_isTarget_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v_a_1545_; lean_object* v___f_1546_; lean_object* v___x_1547_; 
v___x_1541_ = lean_unsigned_to_nat(0u);
v___x_1542_ = ((lean_object*)(l_Lean_Meta_setMVarUserNamesAt___closed__0));
v___x_1543_ = lean_st_mk_ref(v___x_1542_);
v___x_1544_ = l_Lean_instantiateMVars___at___00Lean_Meta_setMVarUserNamesAt_spec__3___redArg(v_e_1534_, v_a_1537_);
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref(v___x_1544_);
lean_inc(v___x_1543_);
v___f_1546_ = lean_alloc_closure((void*)(l_Lean_Meta_setMVarUserNamesAt___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1546_, 0, v___x_1543_);
lean_closure_set(v___f_1546_, 1, v_isTarget_1535_);
lean_closure_set(v___f_1546_, 2, v___x_1541_);
v___x_1547_ = l_Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4(v_a_1545_, v___f_1546_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1555_; 
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1555_ == 0)
{
lean_object* v_unused_1556_; 
v_unused_1556_ = lean_ctor_get(v___x_1547_, 0);
lean_dec(v_unused_1556_);
v___x_1549_ = v___x_1547_;
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
else
{
lean_dec(v___x_1547_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1551_ = lean_st_ref_get(v___x_1543_);
lean_dec(v___x_1543_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1551_);
v___x_1553_ = v___x_1549_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec(v___x_1543_);
v_a_1557_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1547_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1547_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___boxed(lean_object* v_e_1565_, lean_object* v_isTarget_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_Meta_setMVarUserNamesAt(v_e_1565_, v_isTarget_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
lean_dec(v_a_1570_);
lean_dec_ref(v_a_1569_);
lean_dec(v_a_1568_);
lean_dec_ref(v_a_1567_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2(lean_object* v_upperBound_1573_, lean_object* v___x_1574_, lean_object* v_val_1575_, lean_object* v_e_1576_, lean_object* v_isTarget_1577_, lean_object* v_inst_1578_, lean_object* v_R_1579_, lean_object* v_a_1580_, lean_object* v_b_1581_, lean_object* v_c_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___redArg(v_upperBound_1573_, v___x_1574_, v_val_1575_, v_e_1576_, v_isTarget_1577_, v_a_1580_, v_b_1581_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2___boxed(lean_object* v_upperBound_1589_, lean_object* v___x_1590_, lean_object* v_val_1591_, lean_object* v_e_1592_, lean_object* v_isTarget_1593_, lean_object* v_inst_1594_, lean_object* v_R_1595_, lean_object* v_a_1596_, lean_object* v_b_1597_, lean_object* v_c_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_setMVarUserNamesAt_spec__2(v_upperBound_1589_, v___x_1590_, v_val_1591_, v_e_1592_, v_isTarget_1593_, v_inst_1594_, v_R_1595_, v_a_1596_, v_b_1597_, v_c_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec_ref(v_isTarget_1593_);
lean_dec_ref(v_e_1592_);
lean_dec_ref(v___x_1590_);
lean_dec(v_upperBound_1589_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7(lean_object* v_00_u03b2_1605_, lean_object* v_m_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___redArg(v_m_1606_, v_a_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7___boxed(lean_object* v_00_u03b2_1609_, lean_object* v_m_1610_, lean_object* v_a_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7(v_00_u03b2_1609_, v_m_1610_, v_a_1611_);
lean_dec_ref(v_a_1611_);
lean_dec_ref(v_m_1610_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_1613_, lean_object* v_m_1614_, lean_object* v_a_1615_, lean_object* v_b_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8___redArg(v_m_1614_, v_a_1615_, v_b_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8(lean_object* v_00_u03b2_1618_, lean_object* v_a_1619_, lean_object* v_x_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___redArg(v_a_1619_, v_x_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03b2_1622_, lean_object* v_a_1623_, lean_object* v_x_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__7_spec__8(v_00_u03b2_1622_, v_a_1623_, v_x_1624_);
lean_dec(v_x_1624_);
lean_dec_ref(v_a_1623_);
return v_res_1625_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_1626_, lean_object* v_a_1627_, lean_object* v_x_1628_){
_start:
{
uint8_t v___x_1629_; 
v___x_1629_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___redArg(v_a_1627_, v_x_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b2_1630_, lean_object* v_a_1631_, lean_object* v_x_1632_){
_start:
{
uint8_t v_res_1633_; lean_object* v_r_1634_; 
v_res_1633_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__10(v_00_u03b2_1630_, v_a_1631_, v_x_1632_);
lean_dec(v_x_1632_);
lean_dec_ref(v_a_1631_);
v_r_1634_ = lean_box(v_res_1633_);
return v_r_1634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11(lean_object* v_00_u03b2_1635_, lean_object* v_data_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11___redArg(v_data_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12(lean_object* v_00_u03b2_1638_, lean_object* v_a_1639_, lean_object* v_b_1640_, lean_object* v_x_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__12___redArg(v_a_1639_, v_b_1640_, v_x_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16(lean_object* v_00_u03b1_1643_, lean_object* v_name_1644_, uint8_t v_bi_1645_, lean_object* v_type_1646_, lean_object* v_k_1647_, uint8_t v_kind_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___redArg(v_name_1644_, v_bi_1645_, v_type_1646_, v_k_1647_, v_kind_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1656_, lean_object* v_name_1657_, lean_object* v_bi_1658_, lean_object* v_type_1659_, lean_object* v_k_1660_, lean_object* v_kind_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
uint8_t v_bi_boxed_1668_; uint8_t v_kind_boxed_1669_; lean_object* v_res_1670_; 
v_bi_boxed_1668_ = lean_unbox(v_bi_1658_);
v_kind_boxed_1669_ = lean_unbox(v_kind_1661_);
v_res_1670_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__9_spec__14_spec__16(v_00_u03b1_1656_, v_name_1657_, v_bi_boxed_1668_, v_type_1659_, v_k_1660_, v_kind_boxed_1669_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21(lean_object* v_00_u03b1_1671_, lean_object* v_name_1672_, lean_object* v_type_1673_, lean_object* v_val_1674_, lean_object* v_k_1675_, uint8_t v_nondep_1676_, uint8_t v_kind_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___redArg(v_name_1672_, v_type_1673_, v_val_1674_, v_k_1675_, v_nondep_1676_, v_kind_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21___boxed(lean_object* v_00_u03b1_1685_, lean_object* v_name_1686_, lean_object* v_type_1687_, lean_object* v_val_1688_, lean_object* v_k_1689_, lean_object* v_nondep_1690_, lean_object* v_kind_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
uint8_t v_nondep_boxed_1698_; uint8_t v_kind_boxed_1699_; lean_object* v_res_1700_; 
v_nondep_boxed_1698_ = lean_unbox(v_nondep_1690_);
v_kind_boxed_1699_ = lean_unbox(v_kind_1691_);
v_res_1700_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__11_spec__18_spec__21(v_00_u03b1_1685_, v_name_1686_, v_type_1687_, v_val_1688_, v_k_1689_, v_nondep_boxed_1698_, v_kind_boxed_1699_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_1701_, lean_object* v_i_1702_, lean_object* v_source_1703_, lean_object* v_target_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12___redArg(v_i_1702_, v_source_1703_, v_target_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16(lean_object* v_00_u03b2_1706_, lean_object* v_x_1707_, lean_object* v_x_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachExpr___at___00Lean_Meta_setMVarUserNamesAt_spec__4_spec__5_spec__6_spec__8_spec__11_spec__12_spec__16___redArg(v_x_1707_, v_x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(lean_object* v_as_1710_, size_t v_sz_1711_, size_t v_i_1712_, lean_object* v_b_1713_, lean_object* v___y_1714_){
_start:
{
uint8_t v___x_1716_; 
v___x_1716_ = lean_usize_dec_lt(v_i_1712_, v_sz_1711_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1717_, 0, v_b_1713_);
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; lean_object* v_mctx_1719_; lean_object* v_cache_1720_; lean_object* v_zetaDeltaFVarIds_1721_; lean_object* v_postponed_1722_; lean_object* v_diag_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1738_; 
v___x_1718_ = lean_st_ref_take(v___y_1714_);
v_mctx_1719_ = lean_ctor_get(v___x_1718_, 0);
v_cache_1720_ = lean_ctor_get(v___x_1718_, 1);
v_zetaDeltaFVarIds_1721_ = lean_ctor_get(v___x_1718_, 2);
v_postponed_1722_ = lean_ctor_get(v___x_1718_, 3);
v_diag_1723_ = lean_ctor_get(v___x_1718_, 4);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1725_ = v___x_1718_;
v_isShared_1726_ = v_isSharedCheck_1738_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_diag_1723_);
lean_inc(v_postponed_1722_);
lean_inc(v_zetaDeltaFVarIds_1721_);
lean_inc(v_cache_1720_);
lean_inc(v_mctx_1719_);
lean_dec(v___x_1718_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1738_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v_a_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; 
v_a_1727_ = lean_array_uget_borrowed(v_as_1710_, v_i_1712_);
v___x_1728_ = lean_box(0);
lean_inc(v_a_1727_);
v___x_1729_ = l_Lean_MetavarContext_setMVarUserNameTemporarily(v_mctx_1719_, v_a_1727_, v___x_1728_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1729_);
v___x_1731_ = v___x_1725_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v_cache_1720_);
lean_ctor_set(v_reuseFailAlloc_1737_, 2, v_zetaDeltaFVarIds_1721_);
lean_ctor_set(v_reuseFailAlloc_1737_, 3, v_postponed_1722_);
lean_ctor_set(v_reuseFailAlloc_1737_, 4, v_diag_1723_);
v___x_1731_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; size_t v___x_1734_; size_t v___x_1735_; 
v___x_1732_ = lean_st_ref_put(v___y_1714_, v___x_1731_);
v___x_1733_ = lean_box(0);
v___x_1734_ = ((size_t)1ULL);
v___x_1735_ = lean_usize_add(v_i_1712_, v___x_1734_);
v_i_1712_ = v___x_1735_;
v_b_1713_ = v___x_1733_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg___boxed(lean_object* v_as_1739_, lean_object* v_sz_1740_, lean_object* v_i_1741_, lean_object* v_b_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
size_t v_sz_boxed_1745_; size_t v_i_boxed_1746_; lean_object* v_res_1747_; 
v_sz_boxed_1745_ = lean_unbox_usize(v_sz_1740_);
lean_dec(v_sz_1740_);
v_i_boxed_1746_ = lean_unbox_usize(v_i_1741_);
lean_dec(v_i_1741_);
v_res_1747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_as_1739_, v_sz_boxed_1745_, v_i_boxed_1746_, v_b_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v_as_1739_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_resetMVarUserNames(lean_object* v_toReset_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v___x_1754_; size_t v_sz_1755_; size_t v___x_1756_; lean_object* v___x_1757_; 
v___x_1754_ = lean_box(0);
v_sz_1755_ = lean_array_size(v_toReset_1748_);
v___x_1756_ = ((size_t)0ULL);
v___x_1757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_toReset_1748_, v_sz_1755_, v___x_1756_, v___x_1754_, v_a_1750_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1764_ == 0)
{
lean_object* v_unused_1765_; 
v_unused_1765_ = lean_ctor_get(v___x_1757_, 0);
lean_dec(v_unused_1765_);
v___x_1759_ = v___x_1757_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_dec(v___x_1757_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1754_);
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1754_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
else
{
return v___x_1757_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_resetMVarUserNames___boxed(lean_object* v_toReset_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_Meta_resetMVarUserNames(v_toReset_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
lean_dec_ref(v_toReset_1766_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0(lean_object* v_as_1773_, size_t v_sz_1774_, size_t v_i_1775_, lean_object* v_b_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___redArg(v_as_1773_, v_sz_1774_, v_i_1775_, v_b_1776_, v___y_1778_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0___boxed(lean_object* v_as_1783_, lean_object* v_sz_1784_, lean_object* v_i_1785_, lean_object* v_b_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
size_t v_sz_boxed_1792_; size_t v_i_boxed_1793_; lean_object* v_res_1794_; 
v_sz_boxed_1792_ = lean_unbox_usize(v_sz_1784_);
lean_dec(v_sz_1784_);
v_i_boxed_1793_ = lean_unbox_usize(v_i_1785_);
lean_dec(v_i_1785_);
v_res_1794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_resetMVarUserNames_spec__0(v_as_1783_, v_sz_boxed_1792_, v_i_boxed_1793_, v_b_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec_ref(v_as_1783_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(lean_object* v_x_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
if (lean_obj_tag(v_x_1795_) == 2)
{
lean_object* v_mvarId_1801_; lean_object* v___x_1802_; 
v_mvarId_1801_ = lean_ctor_get(v_x_1795_, 0);
lean_inc(v_mvarId_1801_);
lean_dec_ref_known(v_x_1795_, 1);
v___x_1802_ = l_Lean_MVarId_getDecl(v_mvarId_1801_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1813_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1813_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1813_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v_userName_1807_; uint8_t v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1811_; 
v_userName_1807_ = lean_ctor_get(v_a_1803_, 0);
lean_inc(v_userName_1807_);
lean_dec(v_a_1803_);
v___x_1808_ = l_Lean_Name_isAnonymous(v_userName_1807_);
lean_dec(v_userName_1807_);
v___x_1809_ = lean_box(v___x_1808_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1809_);
v___x_1811_ = v___x_1805_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
v_a_1814_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1802_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1802_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
else
{
uint8_t v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_dec_ref(v_x_1795_);
v___x_1822_ = 0;
v___x_1823_ = lean_box(v___x_1822_);
v___x_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
return v___x_1824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0___boxed(lean_object* v_x_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(v_x_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__0(lean_object* v_val_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_x3f_1837_){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = lean_st_ref_get(v_val_1832_);
v___x_1840_ = l_Lean_Meta_resetMVarUserNames(v___x_1839_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
lean_dec(v___x_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__0___boxed(lean_object* v_val_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_x3f_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Lean_Meta_mkForallFVars_x27___lam__0(v_val_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_x3f_1846_);
lean_dec(v_a_x3f_1846_);
lean_dec(v_a_1845_);
lean_dec_ref(v_a_1844_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_val_1841_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(lean_object* v_xs_1849_, lean_object* v_as_1850_, size_t v_sz_1851_, size_t v_i_1852_, lean_object* v_b_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
uint8_t v___x_1860_; 
v___x_1860_ = lean_usize_dec_lt(v_i_1852_, v_sz_1851_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; 
lean_dec_ref(v_xs_1849_);
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v_b_1853_);
return v___x_1861_;
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1863_; 
v_a_1862_ = lean_array_uget_borrowed(v_as_1850_, v_i_1852_);
lean_inc(v___y_1858_);
lean_inc_ref(v___y_1857_);
lean_inc(v___y_1856_);
lean_inc_ref(v___y_1855_);
lean_inc(v_a_1862_);
v___x_1863_ = lean_infer_type(v_a_1862_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1865_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1863_, 1);
lean_inc_ref(v_xs_1849_);
v___x_1865_ = l_Lean_Meta_setMVarUserNamesAt(v_a_1864_, v_xs_1849_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; size_t v___x_1871_; size_t v___x_1872_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v___x_1865_, 1);
v___x_1867_ = lean_st_ref_take(v___y_1854_);
v___x_1868_ = l_Array_append___redArg(v___x_1867_, v_a_1866_);
lean_dec(v_a_1866_);
v___x_1869_ = lean_st_ref_put(v___y_1854_, v___x_1868_);
v___x_1870_ = lean_box(0);
v___x_1871_ = ((size_t)1ULL);
v___x_1872_ = lean_usize_add(v_i_1852_, v___x_1871_);
v_i_1852_ = v___x_1872_;
v_b_1853_ = v___x_1870_;
goto _start;
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec_ref(v_xs_1849_);
v_a_1874_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1865_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1865_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec_ref(v_xs_1849_);
v_a_1882_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1863_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1863_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2___boxed(lean_object* v_xs_1890_, lean_object* v_as_1891_, lean_object* v_sz_1892_, lean_object* v_i_1893_, lean_object* v_b_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
size_t v_sz_boxed_1901_; size_t v_i_boxed_1902_; lean_object* v_res_1903_; 
v_sz_boxed_1901_ = lean_unbox_usize(v_sz_1892_);
lean_dec(v_sz_1892_);
v_i_boxed_1902_ = lean_unbox_usize(v_i_1893_);
lean_dec(v_i_1893_);
v_res_1903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(v_xs_1890_, v_as_1891_, v_sz_boxed_1901_, v_i_boxed_1902_, v_b_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v_as_1891_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(lean_object* v_xs_1904_, lean_object* v_as_1905_, size_t v_sz_1906_, size_t v_i_1907_, lean_object* v_b_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
uint8_t v___x_1915_; 
v___x_1915_ = lean_usize_dec_lt(v_i_1907_, v_sz_1906_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; 
lean_dec_ref(v_xs_1904_);
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_b_1908_);
return v___x_1916_;
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1918_; 
v_a_1917_ = lean_array_uget_borrowed(v_as_1905_, v_i_1907_);
lean_inc(v___y_1913_);
lean_inc_ref(v___y_1912_);
lean_inc(v___y_1911_);
lean_inc_ref(v___y_1910_);
lean_inc(v_a_1917_);
v___x_1918_ = lean_infer_type(v_a_1917_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1920_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref_known(v___x_1918_, 1);
lean_inc_ref(v_xs_1904_);
v___x_1920_ = l_Lean_Meta_setMVarUserNamesAt(v_a_1919_, v_xs_1904_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; size_t v___x_1926_; size_t v___x_1927_; lean_object* v___x_1928_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v___x_1922_ = lean_st_ref_take(v___y_1909_);
v___x_1923_ = l_Array_append___redArg(v___x_1922_, v_a_1921_);
lean_dec(v_a_1921_);
v___x_1924_ = lean_st_ref_put(v___y_1909_, v___x_1923_);
v___x_1925_ = lean_box(0);
v___x_1926_ = ((size_t)1ULL);
v___x_1927_ = lean_usize_add(v_i_1907_, v___x_1926_);
v___x_1928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2_spec__2(v_xs_1904_, v_as_1905_, v_sz_1906_, v___x_1927_, v___x_1925_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
return v___x_1928_;
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec_ref(v_xs_1904_);
v_a_1929_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1920_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1920_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec_ref(v_xs_1904_);
v_a_1937_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1918_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1918_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2___boxed(lean_object* v_xs_1945_, lean_object* v_as_1946_, lean_object* v_sz_1947_, lean_object* v_i_1948_, lean_object* v_b_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
size_t v_sz_boxed_1956_; size_t v_i_boxed_1957_; lean_object* v_res_1958_; 
v_sz_boxed_1956_ = lean_unbox_usize(v_sz_1947_);
lean_dec(v_sz_1947_);
v_i_boxed_1957_ = lean_unbox_usize(v_i_1948_);
lean_dec(v_i_1948_);
v_res_1958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(v_xs_1945_, v_as_1946_, v_sz_boxed_1956_, v_i_boxed_1957_, v_b_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v_as_1946_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(lean_object* v_as_1959_, size_t v_i_1960_, size_t v_stop_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
uint8_t v___x_1967_; 
v___x_1967_ = lean_usize_dec_eq(v_i_1960_, v_stop_1961_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = lean_array_uget_borrowed(v_as_1959_, v_i_1960_);
lean_inc(v___x_1968_);
v___x_1969_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___00Lean_Meta_mkForallFVars_x27_spec__0(v___x_1968_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1981_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_1981_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1981_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
uint8_t v___x_1974_; 
v___x_1974_ = lean_unbox(v_a_1970_);
if (v___x_1974_ == 0)
{
size_t v___x_1975_; size_t v___x_1976_; 
lean_del_object(v___x_1972_);
lean_dec(v_a_1970_);
v___x_1975_ = ((size_t)1ULL);
v___x_1976_ = lean_usize_add(v_i_1960_, v___x_1975_);
v_i_1960_ = v___x_1976_;
goto _start;
}
else
{
lean_object* v___x_1979_; 
if (v_isShared_1973_ == 0)
{
v___x_1979_ = v___x_1972_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1970_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
else
{
return v___x_1969_;
}
}
else
{
uint8_t v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1982_ = 0;
v___x_1983_ = lean_box(v___x_1982_);
v___x_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
return v___x_1984_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1___boxed(lean_object* v_as_1985_, lean_object* v_i_1986_, lean_object* v_stop_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
size_t v_i_boxed_1993_; size_t v_stop_boxed_1994_; lean_object* v_res_1995_; 
v_i_boxed_1993_ = lean_unbox_usize(v_i_1986_);
lean_dec(v_i_1986_);
v_stop_boxed_1994_ = lean_unbox_usize(v_stop_1987_);
lean_dec(v_stop_1987_);
v_res_1995_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(v_as_1985_, v_i_boxed_1993_, v_stop_boxed_1994_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec_ref(v_as_1985_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27(lean_object* v_xs_1996_, lean_object* v_type_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
uint8_t v_a_2004_; lean_object* v___x_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; 
v___x_2008_ = lean_unsigned_to_nat(0u);
v___x_2009_ = lean_array_get_size(v_xs_1996_);
v___x_2010_ = lean_nat_dec_lt(v___x_2008_, v___x_2009_);
if (v___x_2010_ == 0)
{
v_a_2004_ = v___x_2010_;
goto v___jp_2003_;
}
else
{
if (v___x_2010_ == 0)
{
v_a_2004_ = v___x_2010_;
goto v___jp_2003_;
}
else
{
size_t v___x_2011_; size_t v___x_2012_; lean_object* v___x_2013_; 
v___x_2011_ = ((size_t)0ULL);
v___x_2012_ = lean_usize_of_nat(v___x_2009_);
v___x_2013_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_mkForallFVars_x27_spec__1(v_xs_1996_, v___x_2011_, v___x_2012_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; uint8_t v___x_2015_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
v___x_2015_ = lean_unbox(v_a_2014_);
if (v___x_2015_ == 0)
{
uint8_t v___x_2016_; 
v___x_2016_ = lean_unbox(v_a_2014_);
lean_dec(v_a_2014_);
v_a_2004_ = v___x_2016_;
goto v___jp_2003_;
}
else
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v_a_2020_; lean_object* v___x_2039_; size_t v_sz_2040_; lean_object* v___x_2041_; 
lean_dec(v_a_2014_);
v___x_2017_ = ((lean_object*)(l_Lean_Meta_setMVarUserNamesAt___closed__0));
v___x_2018_ = lean_st_mk_ref(v___x_2017_);
v___x_2039_ = lean_box(0);
v_sz_2040_ = lean_array_size(v_xs_1996_);
lean_inc_ref(v_xs_1996_);
v___x_2041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkForallFVars_x27_spec__2(v_xs_1996_, v_xs_1996_, v_sz_2040_, v___x_2011_, v___x_2039_, v___x_2018_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v___x_2042_; 
lean_dec_ref_known(v___x_2041_, 1);
lean_inc_ref(v_xs_1996_);
lean_inc_ref(v_type_1997_);
v___x_2042_ = l_Lean_Meta_setMVarUserNamesAt(v_type_1997_, v_xs_1996_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; uint8_t v___x_2048_; lean_object* v___x_2049_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2042_, 1);
v___x_2044_ = lean_st_ref_take(v___x_2018_);
v___x_2045_ = l_Array_append___redArg(v___x_2044_, v_a_2043_);
lean_dec(v_a_2043_);
v___x_2046_ = lean_st_ref_put(v___x_2018_, v___x_2045_);
v___x_2047_ = 0;
v___x_2048_ = 1;
v___x_2049_ = l_Lean_Meta_mkForallFVars(v_xs_1996_, v_type_1997_, v___x_2047_, v___x_2010_, v___x_2010_, v___x_2048_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
lean_dec_ref(v_xs_1996_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2075_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2075_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2075_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
lean_inc(v_a_2050_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set_tag(v___x_2052_, 1);
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2056_; 
v___x_2056_ = l_Lean_Meta_mkForallFVars_x27___lam__0(v___x_2018_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v___x_2055_);
lean_dec_ref(v___x_2055_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2064_; 
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; 
v_unused_2065_ = lean_ctor_get(v___x_2056_, 0);
lean_dec(v_unused_2065_);
v___x_2058_ = v___x_2056_;
v_isShared_2059_ = v_isSharedCheck_2064_;
goto v_resetjp_2057_;
}
else
{
lean_dec(v___x_2056_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2064_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2060_ = lean_st_ref_get(v___x_2018_);
lean_dec(v___x_2018_);
lean_dec(v___x_2060_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v_a_2050_);
v___x_2062_ = v___x_2058_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2050_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v_a_2050_);
lean_dec(v___x_2018_);
v_a_2066_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2056_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2056_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
}
else
{
lean_object* v_a_2076_; 
v_a_2076_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2049_, 1);
v_a_2020_ = v_a_2076_;
goto v___jp_2019_;
}
}
else
{
lean_object* v_a_2077_; 
lean_dec_ref(v_type_1997_);
lean_dec_ref(v_xs_1996_);
v_a_2077_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2077_);
lean_dec_ref_known(v___x_2042_, 1);
v_a_2020_ = v_a_2077_;
goto v___jp_2019_;
}
}
else
{
lean_object* v_a_2078_; 
lean_dec_ref(v_type_1997_);
lean_dec_ref(v_xs_1996_);
v_a_2078_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2041_, 1);
v_a_2020_ = v_a_2078_;
goto v___jp_2019_;
}
v___jp_2019_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = lean_box(0);
v___x_2022_ = l_Lean_Meta_mkForallFVars_x27___lam__0(v___x_2018_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v___x_2021_);
lean_dec(v___x_2018_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; 
v_unused_2030_ = lean_ctor_get(v___x_2022_, 0);
lean_dec(v_unused_2030_);
v___x_2024_ = v___x_2022_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_dec(v___x_2022_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
lean_ctor_set_tag(v___x_2024_, 1);
lean_ctor_set(v___x_2024_, 0, v_a_2020_);
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2020_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec_ref(v_a_2020_);
v_a_2031_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2022_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2022_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec_ref(v_type_1997_);
lean_dec_ref(v_xs_1996_);
v_a_2079_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2013_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2013_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
}
v___jp_2003_:
{
uint8_t v___x_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; 
v___x_2005_ = 1;
v___x_2006_ = 1;
v___x_2007_ = l_Lean_Meta_mkForallFVars(v_xs_1996_, v_type_1997_, v_a_2004_, v___x_2005_, v___x_2005_, v___x_2006_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
lean_dec_ref(v_xs_1996_);
return v___x_2007_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___boxed(lean_object* v_xs_2087_, lean_object* v_type_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Lean_Meta_mkForallFVars_x27(v_xs_2087_, v_type_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
lean_dec(v_a_2092_);
lean_dec_ref(v_a_2091_);
lean_dec(v_a_2090_);
lean_dec_ref(v_a_2089_);
return v_res_2094_;
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
