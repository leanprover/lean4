// Lean compiler output
// Module: Lean.Meta.Tactic.Subst
// Imports: Lean.Meta.AppBuilder Lean.Meta.MatchUtil Lean.Meta.Tactic.Util Lean.Meta.Tactic.Revert Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Clear Lean.Meta.Tactic.FVarSubst
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
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_hashMVarId____x40_Lean_Expr___hyg_1872____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subst_substEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__2___closed__24;
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__2___closed__12;
static lean_object* l_Lean_Meta_substCore___lam__1___closed__2;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__6;
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_substCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_heqToEq___lam__0___closed__1;
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_substCore_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__1___closed__3;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substVar___lam__0___closed__2;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_substCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0___closed__0;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__3;
static lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0;
static lean_object* l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___Lean_Meta_substVar_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__2___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_substCore_spec__11___boxed(lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__20;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_beqFVarId____x40_Lean_Expr___hyg_1504_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1___boxed(lean_object**);
static lean_object* l_Lean_Meta_substCore___lam__2___closed__8;
static lean_object* l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__2___closed__29;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__17;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__1;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__1___closed__1;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__19;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_substCore_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__2___closed__30;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substVar___lam__0___closed__1;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substVar___lam__0___closed__0;
static lean_object* l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg___closed__0;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_subst_substEq___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__2___closed__15;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__2___closed__31;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_substCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_substVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__2___closed__9;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__25;
LEAN_EXPORT lean_object* l_Lean_Meta_subst_substEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__2___closed__5;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__2___closed__7;
static lean_object* l_Lean_Meta_heqToEq___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_substCore_spec__11(size_t, size_t, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3853_(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__2___closed__11;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__0;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__2___closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_Meta_substCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__4;
static lean_object* l_Lean_Meta_subst_substEq___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_substCore_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__3;
static lean_object* l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___lam__0___boxed(lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__2___closed__2;
static lean_object* l_Lean_Meta_substVar___lam__0___closed__5;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_substCore_spec__12(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_substCore_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__2___closed__26;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_Meta_substCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Meta_substCore_spec__1___closed__0;
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__2___closed__14;
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substVar___lam__0___closed__4;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t l_Lean_beqMVarId____x40_Lean_Expr___hyg_1814_(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substVar___lam__0___closed__3;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__4;
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__1___closed__4;
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__2___closed__21;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__2;
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_subst_substEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__0;
static lean_object* l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg___closed__1;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__1___closed__9;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__27;
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_substCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_subst_substEq___lam__0___closed__3;
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_substCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__1___closed__5;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__23;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_Meta_substCore_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___Lean_Meta_substVar_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_beqMVarId____x40_Lean_Expr___hyg_1814____boxed(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_Meta_substCore_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_substCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__2___closed__22;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__28;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_subst_substEq___lam__0___closed__1;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__16;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_substCore___lam__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_substCore_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_6 = lean_st_ref_get(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
lean_dec(x_7);
x_10 = l_Lean_instantiateMVarsCore(x_9, x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_st_ref_take(x_2, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_12);
x_18 = lean_st_ref_set(x_2, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_11);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_14, 1);
x_24 = lean_ctor_get(x_14, 2);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_st_ref_set(x_2, x_27, x_15);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_substCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___Lean_Meta_substCore_spec__0___redArg(x_1, x_3, x_6);
return x_7;
}
}
static lean_object* _init_l_panic___at___Lean_Meta_substCore_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_substCore_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at___Lean_Meta_substCore_spec__1___closed__0;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_Meta_substCore_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_6, x_9);
if (x_10 == 1)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_6, x_12);
lean_dec(x_6);
x_14 = lean_nat_sub(x_5, x_13);
x_15 = lean_nat_sub(x_14, x_12);
lean_dec(x_14);
x_16 = lean_nat_add(x_15, x_1);
lean_inc(x_2);
x_17 = lean_array_get(x_2, x_3, x_16);
lean_dec(x_16);
x_18 = lean_array_fget(x_4, x_15);
lean_dec(x_15);
x_19 = l_Lean_mkFVar(x_18);
x_20 = l_Lean_Meta_FVarSubst_insert(x_7, x_17, x_19);
x_6 = x_13;
x_7 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_Meta_substCore_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Nat_foldM_loop___at___Lean_Meta_substCore_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 12);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3___redArg(x_1, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_substCore_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
lean_inc_ref(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_4, 2);
lean_inc(x_23);
lean_inc_ref(x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_3, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_ctor_get(x_4, 2);
lean_inc(x_35);
lean_inc_ref(x_34);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_1);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
}
static double _init_l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_substCore_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_substCore_spec__4_spec__4(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 4);
lean_inc_ref(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_13, 4);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; double x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__0;
x_23 = 0;
x_24 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__1;
x_25 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_float(x_25, sizeof(void*)*2, x_22);
lean_ctor_set_float(x_25, sizeof(void*)*2 + 8, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_23);
x_26 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__2;
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_27);
lean_ctor_set(x_12, 0, x_8);
x_28 = l_Lean_PersistentArray_push___redArg(x_21, x_12);
lean_ctor_set(x_14, 0, x_28);
x_29 = lean_st_ref_set(x_6, x_13, x_16);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint64_t x_36; lean_object* x_37; double x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_37 = lean_ctor_get(x_14, 0);
lean_inc(x_37);
lean_dec(x_14);
x_38 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__0;
x_39 = 0;
x_40 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__1;
x_41 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set_float(x_41, sizeof(void*)*2, x_38);
lean_ctor_set_float(x_41, sizeof(void*)*2 + 8, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 16, x_39);
x_42 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__2;
x_43 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_10);
lean_ctor_set(x_43, 2, x_42);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_43);
lean_ctor_set(x_12, 0, x_8);
x_44 = l_Lean_PersistentArray_push___redArg(x_37, x_12);
x_45 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint64(x_45, sizeof(void*)*1, x_36);
lean_ctor_set(x_13, 4, x_45);
x_46 = lean_st_ref_set(x_6, x_13, x_16);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint64_t x_59; lean_object* x_60; lean_object* x_61; double x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get(x_13, 1);
x_53 = lean_ctor_get(x_13, 2);
x_54 = lean_ctor_get(x_13, 3);
x_55 = lean_ctor_get(x_13, 5);
x_56 = lean_ctor_get(x_13, 6);
x_57 = lean_ctor_get(x_13, 7);
x_58 = lean_ctor_get(x_13, 8);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_13);
x_59 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_60 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_60);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_61 = x_14;
} else {
 lean_dec_ref(x_14);
 x_61 = lean_box(0);
}
x_62 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__0;
x_63 = 0;
x_64 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__1;
x_65 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_float(x_65, sizeof(void*)*2, x_62);
lean_ctor_set_float(x_65, sizeof(void*)*2 + 8, x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 16, x_63);
x_66 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__2;
x_67 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_10);
lean_ctor_set(x_67, 2, x_66);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_67);
lean_ctor_set(x_12, 0, x_8);
x_68 = l_Lean_PersistentArray_push___redArg(x_60, x_12);
if (lean_is_scalar(x_61)) {
 x_69 = lean_alloc_ctor(0, 1, 8);
} else {
 x_69 = x_61;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set_uint64(x_69, sizeof(void*)*1, x_59);
x_70 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_70, 0, x_51);
lean_ctor_set(x_70, 1, x_52);
lean_ctor_set(x_70, 2, x_53);
lean_ctor_set(x_70, 3, x_54);
lean_ctor_set(x_70, 4, x_69);
lean_ctor_set(x_70, 5, x_55);
lean_ctor_set(x_70, 6, x_56);
lean_ctor_set(x_70, 7, x_57);
lean_ctor_set(x_70, 8, x_58);
x_71 = lean_st_ref_set(x_6, x_70, x_16);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
x_74 = lean_box(0);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; double x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_76 = lean_ctor_get(x_12, 1);
lean_inc(x_76);
lean_dec(x_12);
x_77 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_13, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_13, 3);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_13, 5);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_13, 6);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_13, 7);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_13, 8);
lean_inc_ref(x_84);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 lean_ctor_release(x_13, 6);
 lean_ctor_release(x_13, 7);
 lean_ctor_release(x_13, 8);
 x_85 = x_13;
} else {
 lean_dec_ref(x_13);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_87 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_87);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_88 = x_14;
} else {
 lean_dec_ref(x_14);
 x_88 = lean_box(0);
}
x_89 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__0;
x_90 = 0;
x_91 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__1;
x_92 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_float(x_92, sizeof(void*)*2, x_89);
lean_ctor_set_float(x_92, sizeof(void*)*2 + 8, x_89);
lean_ctor_set_uint8(x_92, sizeof(void*)*2 + 16, x_90);
x_93 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__2;
x_94 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_10);
lean_ctor_set(x_94, 2, x_93);
lean_inc(x_8);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_8);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_PersistentArray_push___redArg(x_87, x_95);
if (lean_is_scalar(x_88)) {
 x_97 = lean_alloc_ctor(0, 1, 8);
} else {
 x_97 = x_88;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set_uint64(x_97, sizeof(void*)*1, x_86);
if (lean_is_scalar(x_85)) {
 x_98 = lean_alloc_ctor(0, 9, 0);
} else {
 x_98 = x_85;
}
lean_ctor_set(x_98, 0, x_77);
lean_ctor_set(x_98, 1, x_78);
lean_ctor_set(x_98, 2, x_79);
lean_ctor_set(x_98, 3, x_80);
lean_ctor_set(x_98, 4, x_97);
lean_ctor_set(x_98, 5, x_81);
lean_ctor_set(x_98, 6, x_82);
lean_ctor_set(x_98, 7, x_83);
lean_ctor_set(x_98, 8, x_84);
x_99 = lean_st_ref_set(x_6, x_98, x_76);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
x_102 = lean_box(0);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_beqFVarId____x40_Lean_Expr___hyg_1504_(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_34; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_40 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_40);
lean_dec(x_7);
x_41 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___lam__0___boxed), 1, 0);
x_42 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_42, 0, x_2);
x_43 = l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__4;
lean_inc_ref(x_40);
lean_ctor_set(x_5, 1, x_40);
lean_ctor_set(x_5, 0, x_43);
x_44 = l_Lean_Expr_hasFVar(x_1);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = l_Lean_Expr_hasMVar(x_1);
if (x_45 == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_1);
x_9 = x_45;
x_10 = x_40;
goto block_33;
}
else
{
lean_object* x_46; 
lean_dec_ref(x_40);
x_46 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_42, x_41, x_1, x_5);
x_34 = x_46;
goto block_39;
}
}
else
{
lean_object* x_47; 
lean_dec_ref(x_40);
x_47 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_42, x_41, x_1, x_5);
x_34 = x_47;
goto block_39;
}
block_33:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_take(x_3, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_10);
x_16 = lean_st_ref_set(x_3, x_12, x_13);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(x_9);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(x_9);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_12, 1);
x_24 = lean_ctor_get(x_12, 2);
x_25 = lean_ctor_get(x_12, 3);
x_26 = lean_ctor_get(x_12, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_st_ref_set(x_3, x_27, x_13);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_box(x_9);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
block_39:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_ctor_get(x_35, 1);
lean_inc_ref(x_37);
lean_dec(x_35);
x_38 = lean_unbox(x_36);
lean_dec(x_36);
x_9 = x_38;
x_10 = x_37;
goto block_33;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_67; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_48 = lean_ctor_get(x_5, 0);
x_49 = lean_ctor_get(x_5, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_5);
x_73 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_73);
lean_dec(x_48);
x_74 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___lam__0___boxed), 1, 0);
x_75 = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_75, 0, x_2);
x_76 = l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__4;
lean_inc_ref(x_73);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_73);
x_78 = l_Lean_Expr_hasFVar(x_1);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Expr_hasMVar(x_1);
if (x_79 == 0)
{
lean_dec_ref(x_77);
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_1);
x_50 = x_79;
x_51 = x_73;
goto block_66;
}
else
{
lean_object* x_80; 
lean_dec_ref(x_73);
x_80 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_75, x_74, x_1, x_77);
x_67 = x_80;
goto block_72;
}
}
else
{
lean_object* x_81; 
lean_dec_ref(x_73);
x_81 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(x_75, x_74, x_1, x_77);
x_67 = x_81;
goto block_72;
}
block_66:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_52 = lean_st_ref_take(x_3, x_49);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = lean_ctor_get(x_53, 1);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_53, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_53, 3);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_53, 4);
lean_inc_ref(x_58);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 lean_ctor_release(x_53, 3);
 lean_ctor_release(x_53, 4);
 x_59 = x_53;
} else {
 lean_dec_ref(x_53);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 5, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_51);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_60, 2, x_56);
lean_ctor_set(x_60, 3, x_57);
lean_ctor_set(x_60, 4, x_58);
x_61 = lean_st_ref_set(x_3, x_60, x_54);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(x_50);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
block_72:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec_ref(x_67);
x_70 = lean_ctor_get(x_68, 1);
lean_inc_ref(x_70);
lean_dec(x_68);
x_71 = lean_unbox(x_69);
lean_dec(x_69);
x_50 = x_71;
x_51 = x_70;
goto block_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg(x_1, x_2, x_4, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_beqMVarId____x40_Lean_Expr___hyg_1814____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_hashMVarId____x40_Lean_Expr___hyg_1872____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_7, 7);
x_13 = l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg___closed__0;
x_14 = l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg___closed__1;
x_15 = l_Lean_PersistentHashMap_insert___redArg(x_13, x_14, x_12, x_1, x_2);
lean_ctor_set(x_7, 7, x_15);
x_16 = lean_st_ref_set(x_3, x_6, x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
x_25 = lean_ctor_get(x_7, 2);
x_26 = lean_ctor_get(x_7, 3);
x_27 = lean_ctor_get(x_7, 4);
x_28 = lean_ctor_get(x_7, 5);
x_29 = lean_ctor_get(x_7, 6);
x_30 = lean_ctor_get(x_7, 7);
x_31 = lean_ctor_get(x_7, 8);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_32 = l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg___closed__0;
x_33 = l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg___closed__1;
x_34 = l_Lean_PersistentHashMap_insert___redArg(x_32, x_33, x_30, x_1, x_2);
x_35 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set(x_35, 4, x_27);
lean_ctor_set(x_35, 5, x_28);
lean_ctor_set(x_35, 6, x_29);
lean_ctor_set(x_35, 7, x_34);
lean_ctor_set(x_35, 8, x_31);
lean_ctor_set(x_6, 0, x_35);
x_36 = lean_st_ref_set(x_3, x_6, x_8);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_41 = lean_ctor_get(x_6, 1);
x_42 = lean_ctor_get(x_6, 2);
x_43 = lean_ctor_get(x_6, 3);
x_44 = lean_ctor_get(x_6, 4);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_6);
x_45 = lean_ctor_get(x_7, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_7, 3);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_7, 4);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_7, 5);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_7, 6);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_7, 7);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_7, 8);
lean_inc_ref(x_53);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 lean_ctor_release(x_7, 7);
 lean_ctor_release(x_7, 8);
 x_54 = x_7;
} else {
 lean_dec_ref(x_7);
 x_54 = lean_box(0);
}
x_55 = l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg___closed__0;
x_56 = l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg___closed__1;
x_57 = l_Lean_PersistentHashMap_insert___redArg(x_55, x_56, x_52, x_1, x_2);
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(0, 9, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_45);
lean_ctor_set(x_58, 1, x_46);
lean_ctor_set(x_58, 2, x_47);
lean_ctor_set(x_58, 3, x_48);
lean_ctor_set(x_58, 4, x_49);
lean_ctor_set(x_58, 5, x_50);
lean_ctor_set(x_58, 6, x_51);
lean_ctor_set(x_58, 7, x_57);
lean_ctor_set(x_58, 8, x_53);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_41);
lean_ctor_set(x_59, 2, x_42);
lean_ctor_set(x_59, 3, x_43);
lean_ctor_set(x_59, 4, x_44);
x_60 = lean_st_ref_set(x_3, x_59, x_8);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg(x_1, x_2, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8_spec__8___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8_spec__8___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8_spec__8___redArg___lam__0), 7, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8_spec__8(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8_spec__8___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = 0;
x_11 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8_spec__8___redArg(x_1, x_9, x_2, x_3, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_substCore_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_substCore_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___Lean_Meta_substCore_spec__10___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_substCore_spec__11(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_substCore_spec__12(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_MessageData_ofName(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_MessageData_ofName(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
x_13 = l_Lean_Meta_mkEqSymm(x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_Expr_replaceFVar(x_1, x_2, x_14);
lean_dec(x_14);
x_17 = lean_mk_empty_array_with_capacity(x_3);
x_18 = lean_array_push(x_17, x_4);
x_19 = lean_array_push(x_18, x_7);
x_20 = 1;
x_21 = l_Lean_Meta_mkLambdaFVars(x_19, x_16, x_5, x_6, x_5, x_6, x_20, x_8, x_9, x_10, x_11, x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_19);
return x_21;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("after intro rest ", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lam__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Subst", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.substCore", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_substCore___lam__1___closed__7;
x_2 = lean_unsigned_to_nat(22u);
x_3 = lean_unsigned_to_nat(69u);
x_4 = l_Lean_Meta_substCore___lam__1___closed__6;
x_5 = l_Lean_Meta_substCore___lam__1___closed__5;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_h", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lam__1___closed__9;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, uint8_t x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, uint8_t x_18, uint8_t x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25) {
_start:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_191; 
lean_inc(x_1);
x_191 = l_Lean_MVarId_getDecl(x_1, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec_ref(x_191);
lean_inc_ref(x_21);
lean_inc(x_2);
x_194 = l_Lean_FVarId_getDecl___redArg(x_2, x_21, x_23, x_24, x_193);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec_ref(x_194);
x_197 = l_Lean_LocalDecl_type(x_195);
lean_dec(x_195);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
x_198 = l_Lean_Meta_matchEq_x3f(x_197, x_21, x_22, x_23, x_24, x_196);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_192);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec_ref(x_198);
x_201 = l_Lean_Meta_substCore___lam__1___closed__8;
x_202 = l_panic___at___Lean_Meta_substCore_spec__1(x_201, x_21, x_22, x_23, x_24, x_200);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_203 = lean_ctor_get(x_199, 0);
lean_inc(x_203);
lean_dec_ref(x_199);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec(x_203);
x_205 = lean_ctor_get(x_198, 1);
lean_inc(x_205);
lean_dec_ref(x_198);
x_206 = lean_ctor_get(x_204, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_204, 1);
lean_inc(x_207);
lean_dec(x_204);
x_208 = lean_ctor_get(x_192, 2);
lean_inc_ref(x_208);
lean_dec(x_192);
x_209 = lean_box(x_19);
x_210 = lean_box(x_14);
lean_inc_ref(x_11);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_208);
x_211 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__0___boxed), 12, 6);
lean_closure_set(x_211, 0, x_208);
lean_closure_set(x_211, 1, x_5);
lean_closure_set(x_211, 2, x_6);
lean_closure_set(x_211, 3, x_11);
lean_closure_set(x_211, 4, x_209);
lean_closure_set(x_211, 5, x_210);
if (x_18 == 0)
{
lean_dec(x_206);
x_212 = x_207;
goto block_270;
}
else
{
lean_dec(x_207);
x_212 = x_206;
goto block_270;
}
block_270:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_213 = l_Lean_instantiateMVars___at___Lean_Meta_substCore_spec__0___redArg(x_212, x_22, x_205);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec_ref(x_213);
lean_inc(x_2);
lean_inc_ref(x_208);
x_216 = l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg(x_208, x_2, x_22, x_215);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_unbox(x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; 
lean_dec_ref(x_211);
x_219 = lean_ctor_get(x_216, 1);
lean_inc(x_219);
lean_dec_ref(x_216);
x_220 = lean_mk_empty_array_with_capacity(x_20);
lean_inc_ref(x_11);
x_221 = lean_array_push(x_220, x_11);
x_222 = 1;
lean_inc_ref(x_208);
x_223 = l_Lean_Meta_mkLambdaFVars(x_221, x_208, x_19, x_14, x_19, x_14, x_222, x_21, x_22, x_23, x_24, x_219);
lean_dec_ref(x_221);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec_ref(x_223);
lean_inc_ref(x_11);
x_226 = l_Lean_Expr_replaceFVar(x_208, x_11, x_214);
lean_dec_ref(x_208);
x_227 = lean_unbox(x_217);
lean_dec(x_217);
x_174 = x_227;
x_175 = x_214;
x_176 = x_224;
x_177 = x_226;
x_178 = x_21;
x_179 = x_22;
x_180 = x_23;
x_181 = x_24;
x_182 = x_225;
goto block_190;
}
else
{
uint8_t x_228; 
lean_dec(x_217);
lean_dec(x_214);
lean_dec_ref(x_208);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_228 = !lean_is_exclusive(x_223);
if (x_228 == 0)
{
return x_223;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_223, 0);
x_230 = lean_ctor_get(x_223, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_223);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_ctor_get(x_216, 1);
lean_inc(x_232);
lean_dec_ref(x_216);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc(x_214);
x_233 = l_Lean_Meta_mkEqRefl(x_214, x_21, x_22, x_23, x_24, x_232);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec_ref(x_233);
lean_inc_ref(x_11);
x_236 = l_Lean_Expr_replaceFVar(x_208, x_11, x_214);
lean_inc_ref(x_5);
x_237 = l_Lean_Expr_replaceFVar(x_236, x_5, x_234);
lean_dec(x_234);
lean_dec_ref(x_236);
if (x_18 == 0)
{
lean_object* x_238; 
lean_dec_ref(x_208);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
lean_inc_ref(x_11);
lean_inc(x_214);
x_238 = l_Lean_Meta_mkEq(x_214, x_11, x_21, x_22, x_23, x_24, x_235);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec_ref(x_238);
x_241 = l_Lean_Meta_substCore___lam__1___closed__10;
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
x_242 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8___redArg(x_241, x_239, x_211, x_21, x_22, x_23, x_24, x_240);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec_ref(x_242);
x_245 = lean_unbox(x_217);
lean_dec(x_217);
x_174 = x_245;
x_175 = x_214;
x_176 = x_243;
x_177 = x_237;
x_178 = x_21;
x_179 = x_22;
x_180 = x_23;
x_181 = x_24;
x_182 = x_244;
goto block_190;
}
else
{
uint8_t x_246; 
lean_dec_ref(x_237);
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_246 = !lean_is_exclusive(x_242);
if (x_246 == 0)
{
return x_242;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_242, 0);
x_248 = lean_ctor_get(x_242, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_242);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
else
{
uint8_t x_250; 
lean_dec_ref(x_237);
lean_dec(x_217);
lean_dec(x_214);
lean_dec_ref(x_211);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_250 = !lean_is_exclusive(x_238);
if (x_250 == 0)
{
return x_238;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_238, 0);
x_252 = lean_ctor_get(x_238, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_238);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; 
lean_dec_ref(x_211);
x_254 = lean_mk_empty_array_with_capacity(x_6);
lean_inc_ref(x_11);
x_255 = lean_array_push(x_254, x_11);
lean_inc_ref(x_5);
x_256 = lean_array_push(x_255, x_5);
x_257 = 1;
x_258 = l_Lean_Meta_mkLambdaFVars(x_256, x_208, x_19, x_14, x_19, x_14, x_257, x_21, x_22, x_23, x_24, x_235);
lean_dec_ref(x_256);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec_ref(x_258);
x_261 = lean_unbox(x_217);
lean_dec(x_217);
x_174 = x_261;
x_175 = x_214;
x_176 = x_259;
x_177 = x_237;
x_178 = x_21;
x_179 = x_22;
x_180 = x_23;
x_181 = x_24;
x_182 = x_260;
goto block_190;
}
else
{
uint8_t x_262; 
lean_dec_ref(x_237);
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_262 = !lean_is_exclusive(x_258);
if (x_262 == 0)
{
return x_258;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_258, 0);
x_264 = lean_ctor_get(x_258, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_258);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
}
else
{
uint8_t x_266; 
lean_dec(x_217);
lean_dec(x_214);
lean_dec_ref(x_211);
lean_dec_ref(x_208);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_266 = !lean_is_exclusive(x_233);
if (x_266 == 0)
{
return x_233;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_233, 0);
x_268 = lean_ctor_get(x_233, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_233);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
}
}
}
else
{
uint8_t x_271; 
lean_dec(x_192);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_271 = !lean_is_exclusive(x_198);
if (x_271 == 0)
{
return x_198;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_198, 0);
x_273 = lean_ctor_get(x_198, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_198);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
else
{
uint8_t x_275; 
lean_dec(x_192);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_275 = !lean_is_exclusive(x_194);
if (x_275 == 0)
{
return x_194;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_194, 0);
x_277 = lean_ctor_get(x_194, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_194);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
}
else
{
uint8_t x_279; 
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_279 = !lean_is_exclusive(x_191);
if (x_279 == 0)
{
return x_191;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_191, 0);
x_281 = lean_ctor_get(x_191, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_191);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
return x_282;
}
}
block_34:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = l_Lean_Meta_FVarSubst_insert(x_26, x_3, x_29);
x_31 = l_Lean_Meta_FVarSubst_insert(x_30, x_4, x_5);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
block_45:
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_array_get_size(x_35);
lean_inc(x_39);
x_40 = l_Nat_foldM_loop___at___Lean_Meta_substCore_spec__2___redArg(x_6, x_7, x_8, x_35, x_39, x_39, x_9, x_38);
lean_dec(x_39);
lean_dec_ref(x_35);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_37);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_26 = x_41;
x_27 = x_42;
x_28 = x_36;
x_29 = x_11;
goto block_34;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_11);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec_ref(x_40);
x_26 = x_43;
x_27 = x_44;
x_28 = x_36;
x_29 = x_37;
goto block_34;
}
}
block_117:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_array_get_size(x_8);
x_54 = lean_nat_sub(x_53, x_6);
lean_dec(x_53);
lean_inc(x_51);
lean_inc_ref(x_50);
lean_inc(x_49);
lean_inc_ref(x_48);
lean_inc(x_54);
x_55 = l_Lean_Meta_introNCore(x_47, x_54, x_12, x_13, x_14, x_48, x_49, x_50, x_51, x_52);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_56, 0);
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_15);
x_61 = l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3___redArg(x_15, x_50, x_57);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
lean_free_object(x_56);
lean_dec(x_54);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_15);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec_ref(x_61);
x_35 = x_59;
x_36 = x_60;
x_37 = x_46;
x_38 = x_64;
goto block_45;
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_66 = lean_ctor_get(x_61, 1);
x_67 = lean_ctor_get(x_61, 0);
lean_dec(x_67);
x_68 = l_Lean_Meta_substCore___lam__1___closed__1;
x_69 = l_Nat_reprFast(x_54);
x_70 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = l_Lean_MessageData_ofFormat(x_70);
lean_ctor_set_tag(x_61, 7);
lean_ctor_set(x_61, 1, x_71);
lean_ctor_set(x_61, 0, x_68);
x_72 = l_Lean_Meta_substCore___lam__1___closed__3;
lean_ctor_set_tag(x_56, 7);
lean_ctor_set(x_56, 1, x_72);
lean_ctor_set(x_56, 0, x_61);
lean_inc(x_60);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_60);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_56);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_Meta_substCore___lam__1___closed__4;
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4(x_15, x_76, x_48, x_49, x_50, x_51, x_66);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec_ref(x_77);
x_35 = x_59;
x_36 = x_60;
x_37 = x_46;
x_38 = x_78;
goto block_45;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_79 = lean_ctor_get(x_61, 1);
lean_inc(x_79);
lean_dec(x_61);
x_80 = l_Lean_Meta_substCore___lam__1___closed__1;
x_81 = l_Nat_reprFast(x_54);
x_82 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = l_Lean_MessageData_ofFormat(x_82);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Meta_substCore___lam__1___closed__3;
lean_ctor_set_tag(x_56, 7);
lean_ctor_set(x_56, 1, x_85);
lean_ctor_set(x_56, 0, x_84);
lean_inc(x_60);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_60);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_56);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_Meta_substCore___lam__1___closed__4;
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4(x_15, x_89, x_48, x_49, x_50, x_51, x_79);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec_ref(x_90);
x_35 = x_59;
x_36 = x_60;
x_37 = x_46;
x_38 = x_91;
goto block_45;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_56, 0);
x_93 = lean_ctor_get(x_56, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_56);
lean_inc(x_15);
x_94 = l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3___redArg(x_15, x_50, x_57);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_unbox(x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec(x_54);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_15);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec_ref(x_94);
x_35 = x_92;
x_36 = x_93;
x_37 = x_46;
x_38 = x_97;
goto block_45;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_99 = x_94;
} else {
 lean_dec_ref(x_94);
 x_99 = lean_box(0);
}
x_100 = l_Lean_Meta_substCore___lam__1___closed__1;
x_101 = l_Nat_reprFast(x_54);
x_102 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = l_Lean_MessageData_ofFormat(x_102);
if (lean_is_scalar(x_99)) {
 x_104 = lean_alloc_ctor(7, 2, 0);
} else {
 x_104 = x_99;
 lean_ctor_set_tag(x_104, 7);
}
lean_ctor_set(x_104, 0, x_100);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_Meta_substCore___lam__1___closed__3;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
lean_inc(x_93);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_93);
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_Meta_substCore___lam__1___closed__4;
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4(x_15, x_110, x_48, x_49, x_50, x_51, x_98);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec_ref(x_111);
x_35 = x_92;
x_36 = x_93;
x_37 = x_46;
x_38 = x_112;
goto block_45;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_54);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec_ref(x_46);
lean_dec(x_15);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_113 = !lean_is_exclusive(x_55);
if (x_113 == 0)
{
return x_55;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_55, 0);
x_115 = lean_ctor_get(x_55, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_55);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
block_143:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg(x_1, x_120, x_122, x_125);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = l_Lean_Expr_mvarId_x21(x_118);
lean_dec_ref(x_118);
if (x_10 == 0)
{
lean_dec(x_16);
lean_dec(x_2);
x_46 = x_119;
x_47 = x_128;
x_48 = x_121;
x_49 = x_122;
x_50 = x_123;
x_51 = x_124;
x_52 = x_127;
goto block_117;
}
else
{
lean_object* x_129; 
lean_inc(x_124);
lean_inc_ref(x_123);
lean_inc(x_122);
lean_inc_ref(x_121);
x_129 = l_Lean_MVarId_clear(x_128, x_2, x_121, x_122, x_123, x_124, x_127);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec_ref(x_129);
lean_inc(x_124);
lean_inc_ref(x_123);
lean_inc(x_122);
lean_inc_ref(x_121);
x_132 = l_Lean_MVarId_clear(x_130, x_16, x_121, x_122, x_123, x_124, x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec_ref(x_132);
x_46 = x_119;
x_47 = x_133;
x_48 = x_121;
x_49 = x_122;
x_50 = x_123;
x_51 = x_124;
x_52 = x_134;
goto block_117;
}
else
{
uint8_t x_135; 
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec_ref(x_119);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_135 = !lean_is_exclusive(x_132);
if (x_135 == 0)
{
return x_132;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_132, 0);
x_137 = lean_ctor_get(x_132, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_132);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec_ref(x_119);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_139 = !lean_is_exclusive(x_129);
if (x_139 == 0)
{
return x_129;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_129, 0);
x_141 = lean_ctor_get(x_129, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_129);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
block_173:
{
lean_object* x_154; 
lean_inc_ref(x_149);
x_154 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_144, x_17, x_149, x_150, x_151, x_152, x_153);
if (x_146 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec_ref(x_154);
lean_inc(x_152);
lean_inc_ref(x_151);
lean_inc(x_150);
lean_inc_ref(x_149);
lean_inc(x_155);
x_157 = l_Lean_Meta_mkEqNDRec(x_145, x_155, x_148, x_149, x_150, x_151, x_152, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec_ref(x_157);
x_118 = x_155;
x_119 = x_147;
x_120 = x_158;
x_121 = x_149;
x_122 = x_150;
x_123 = x_151;
x_124 = x_152;
x_125 = x_159;
goto block_143;
}
else
{
uint8_t x_160; 
lean_dec(x_155);
lean_dec(x_152);
lean_dec_ref(x_151);
lean_dec(x_150);
lean_dec_ref(x_149);
lean_dec_ref(x_147);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = !lean_is_exclusive(x_157);
if (x_160 == 0)
{
return x_157;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_157, 0);
x_162 = lean_ctor_get(x_157, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_157);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_154, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_154, 1);
lean_inc(x_165);
lean_dec_ref(x_154);
lean_inc(x_152);
lean_inc_ref(x_151);
lean_inc(x_150);
lean_inc_ref(x_149);
lean_inc(x_164);
x_166 = l_Lean_Meta_mkEqRec(x_145, x_164, x_148, x_149, x_150, x_151, x_152, x_165);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec_ref(x_166);
x_118 = x_164;
x_119 = x_147;
x_120 = x_167;
x_121 = x_149;
x_122 = x_150;
x_123 = x_151;
x_124 = x_152;
x_125 = x_168;
goto block_143;
}
else
{
uint8_t x_169; 
lean_dec(x_164);
lean_dec(x_152);
lean_dec_ref(x_151);
lean_dec(x_150);
lean_dec_ref(x_149);
lean_dec_ref(x_147);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_166);
if (x_169 == 0)
{
return x_166;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_166, 0);
x_171 = lean_ctor_get(x_166, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_166);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
block_190:
{
if (x_18 == 0)
{
lean_object* x_183; 
lean_inc(x_181);
lean_inc_ref(x_180);
lean_inc(x_179);
lean_inc_ref(x_178);
lean_inc_ref(x_5);
x_183 = l_Lean_Meta_mkEqSymm(x_5, x_178, x_179, x_180, x_181, x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec_ref(x_183);
x_144 = x_177;
x_145 = x_176;
x_146 = x_174;
x_147 = x_175;
x_148 = x_184;
x_149 = x_178;
x_150 = x_179;
x_151 = x_180;
x_152 = x_181;
x_153 = x_185;
goto block_173;
}
else
{
uint8_t x_186; 
lean_dec(x_181);
lean_dec_ref(x_180);
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec_ref(x_177);
lean_dec_ref(x_176);
lean_dec_ref(x_175);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_186 = !lean_is_exclusive(x_183);
if (x_186 == 0)
{
return x_183;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_183, 0);
x_188 = lean_ctor_get(x_183, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_183);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
else
{
lean_inc_ref(x_5);
x_144 = x_177;
x_145 = x_176;
x_146 = x_174;
x_147 = x_175;
x_148 = x_5;
x_149 = x_178;
x_150 = x_179;
x_151 = x_180;
x_152 = x_181;
x_153 = x_182;
goto block_173;
}
}
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subst", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lam__2___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid equality proof, it is not of the form ", 46, 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lam__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nafter WHNF, variable expected, but obtained", 44, 44);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lam__2___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("argument must be an equality proof", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lam__2___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lam__2___closed__7;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lam__2___closed__8;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reverted variables ", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lam__2___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("after intro2 ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lam__2___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("after revert ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lam__2___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lam__2___closed__17;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' occurs at", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lam__2___closed__19;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_substCore___lam__2___closed__0;
x_2 = l_Lean_Meta_substCore___lam__2___closed__22;
x_3 = l_Lean_Meta_substCore___lam__2___closed__21;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("substituting ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lam__2___closed__24;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" (id: ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lam__2___closed__26;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(") with ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lam__2___closed__28;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(x = t)", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(t = x)", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_1);
x_13 = l_Lean_MVarId_getTag(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_Meta_substCore___lam__2___closed__1;
lean_inc(x_1);
x_17 = l_Lean_MVarId_checkNotAssigned(x_1, x_16, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
lean_inc_ref(x_8);
lean_inc(x_2);
x_19 = l_Lean_FVarId_getDecl___redArg(x_2, x_8, x_10, x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_41; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l_Lean_LocalDecl_type(x_20);
lean_dec(x_20);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_22);
x_41 = l_Lean_Meta_matchEq_x3f(x_22, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_22);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = l_Lean_Meta_substCore___lam__2___closed__9;
x_45 = l_Lean_Meta_throwTacticEx___redArg(x_16, x_1, x_44, x_8, x_9, x_10, x_11, x_43);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_445; 
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_47 = x_42;
} else {
 lean_dec_ref(x_42);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec_ref(x_41);
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_53 = x_48;
} else {
 lean_dec_ref(x_48);
 x_53 = lean_box(0);
}
x_54 = 1;
if (x_6 == 0)
{
lean_inc(x_51);
x_445 = x_51;
goto block_451;
}
else
{
lean_inc(x_52);
x_445 = x_52;
goto block_451;
}
block_81:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_box(x_4);
x_75 = lean_box(x_72);
x_76 = lean_box(x_54);
x_77 = lean_box(x_6);
x_78 = lean_box(x_57);
x_79 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__1___boxed), 25, 20);
lean_closure_set(x_79, 0, x_56);
lean_closure_set(x_79, 1, x_61);
lean_closure_set(x_79, 2, x_68);
lean_closure_set(x_79, 3, x_2);
lean_closure_set(x_79, 4, x_69);
lean_closure_set(x_79, 5, x_70);
lean_closure_set(x_79, 6, x_3);
lean_closure_set(x_79, 7, x_67);
lean_closure_set(x_79, 8, x_5);
lean_closure_set(x_79, 9, x_74);
lean_closure_set(x_79, 10, x_60);
lean_closure_set(x_79, 11, x_58);
lean_closure_set(x_79, 12, x_75);
lean_closure_set(x_79, 13, x_76);
lean_closure_set(x_79, 14, x_64);
lean_closure_set(x_79, 15, x_59);
lean_closure_set(x_79, 16, x_14);
lean_closure_set(x_79, 17, x_77);
lean_closure_set(x_79, 18, x_78);
lean_closure_set(x_79, 19, x_55);
x_80 = l_Lean_MVarId_withContext___at___Lean_Meta_substCore_spec__10___redArg(x_65, x_79, x_63, x_62, x_71, x_66, x_73);
return x_80;
}
block_149:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_100 = lean_array_get(x_3, x_90, x_99);
lean_inc(x_100);
x_101 = l_Lean_mkFVar(x_100);
x_102 = lean_unsigned_to_nat(1u);
lean_inc(x_3);
x_103 = lean_array_get(x_3, x_90, x_102);
lean_dec_ref(x_90);
lean_inc(x_103);
x_104 = l_Lean_mkFVar(x_103);
if (x_7 == 0)
{
lean_dec(x_92);
lean_dec_ref(x_89);
lean_dec(x_53);
x_55 = x_102;
x_56 = x_84;
x_57 = x_83;
x_58 = x_88;
x_59 = x_100;
x_60 = x_101;
x_61 = x_103;
x_62 = x_95;
x_63 = x_94;
x_64 = x_82;
x_65 = x_91;
x_66 = x_97;
x_67 = x_85;
x_68 = x_86;
x_69 = x_104;
x_70 = x_87;
x_71 = x_96;
x_72 = x_93;
x_73 = x_98;
goto block_81;
}
else
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_array_get_size(x_89);
lean_dec_ref(x_89);
x_106 = lean_nat_dec_eq(x_105, x_92);
lean_dec(x_92);
lean_dec(x_105);
if (x_106 == 0)
{
lean_dec(x_53);
x_55 = x_102;
x_56 = x_84;
x_57 = x_83;
x_58 = x_88;
x_59 = x_100;
x_60 = x_101;
x_61 = x_103;
x_62 = x_95;
x_63 = x_94;
x_64 = x_82;
x_65 = x_91;
x_66 = x_97;
x_67 = x_85;
x_68 = x_86;
x_69 = x_104;
x_70 = x_87;
x_71 = x_96;
x_72 = x_93;
x_73 = x_98;
goto block_81;
}
else
{
lean_object* x_107; 
lean_inc(x_91);
x_107 = l_Lean_MVarId_getType(x_91, x_94, x_95, x_96, x_97, x_98);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec_ref(x_107);
lean_inc(x_100);
lean_inc(x_108);
x_110 = l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg(x_108, x_100, x_95, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec_ref(x_110);
lean_inc(x_103);
x_114 = l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg(x_108, x_103, x_95, x_113);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_dec_ref(x_104);
lean_dec_ref(x_101);
lean_dec(x_88);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
if (x_4 == 0)
{
uint8_t x_117; 
lean_dec(x_103);
lean_dec(x_100);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
x_117 = !lean_is_exclusive(x_114);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_114, 0);
lean_dec(x_118);
if (lean_is_scalar(x_53)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_53;
}
lean_ctor_set(x_119, 0, x_5);
lean_ctor_set(x_119, 1, x_91);
lean_ctor_set(x_114, 0, x_119);
return x_114;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_114, 1);
lean_inc(x_120);
lean_dec(x_114);
if (lean_is_scalar(x_53)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_53;
}
lean_ctor_set(x_121, 0, x_5);
lean_ctor_set(x_121, 1, x_91);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_114, 1);
lean_inc(x_123);
lean_dec_ref(x_114);
lean_inc(x_97);
lean_inc_ref(x_96);
lean_inc(x_95);
lean_inc_ref(x_94);
x_124 = l_Lean_MVarId_clear(x_91, x_103, x_94, x_95, x_96, x_97, x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec_ref(x_124);
x_127 = l_Lean_MVarId_clear(x_125, x_100, x_94, x_95, x_96, x_97, x_126);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_127, 0);
if (lean_is_scalar(x_53)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_53;
}
lean_ctor_set(x_130, 0, x_5);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_127, 0, x_130);
return x_127;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_127, 0);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_127);
if (lean_is_scalar(x_53)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_53;
}
lean_ctor_set(x_133, 0, x_5);
lean_ctor_set(x_133, 1, x_131);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
uint8_t x_135; 
lean_dec(x_53);
lean_dec(x_5);
x_135 = !lean_is_exclusive(x_127);
if (x_135 == 0)
{
return x_127;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_127, 0);
x_137 = lean_ctor_get(x_127, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_127);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_100);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec(x_53);
lean_dec(x_5);
x_139 = !lean_is_exclusive(x_124);
if (x_139 == 0)
{
return x_124;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_124, 0);
x_141 = lean_ctor_get(x_124, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_124);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
else
{
lean_object* x_143; 
lean_dec(x_53);
x_143 = lean_ctor_get(x_114, 1);
lean_inc(x_143);
lean_dec_ref(x_114);
x_55 = x_102;
x_56 = x_84;
x_57 = x_83;
x_58 = x_88;
x_59 = x_100;
x_60 = x_101;
x_61 = x_103;
x_62 = x_95;
x_63 = x_94;
x_64 = x_82;
x_65 = x_91;
x_66 = x_97;
x_67 = x_85;
x_68 = x_86;
x_69 = x_104;
x_70 = x_87;
x_71 = x_96;
x_72 = x_93;
x_73 = x_143;
goto block_81;
}
}
else
{
lean_object* x_144; 
lean_dec(x_108);
lean_dec(x_53);
x_144 = lean_ctor_get(x_110, 1);
lean_inc(x_144);
lean_dec_ref(x_110);
x_55 = x_102;
x_56 = x_84;
x_57 = x_83;
x_58 = x_88;
x_59 = x_100;
x_60 = x_101;
x_61 = x_103;
x_62 = x_95;
x_63 = x_94;
x_64 = x_82;
x_65 = x_91;
x_66 = x_97;
x_67 = x_85;
x_68 = x_86;
x_69 = x_104;
x_70 = x_87;
x_71 = x_96;
x_72 = x_93;
x_73 = x_144;
goto block_81;
}
}
else
{
uint8_t x_145; 
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec(x_91);
lean_dec(x_88);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_53);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_145 = !lean_is_exclusive(x_107);
if (x_145 == 0)
{
return x_107;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_107, 0);
x_147 = lean_ctor_get(x_107, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_107);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
}
block_201:
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
lean_inc(x_159);
x_168 = l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3___redArg(x_159, x_165, x_167);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_unbox(x_169);
lean_dec(x_169);
if (x_170 == 0)
{
lean_object* x_171; 
lean_dec(x_159);
lean_dec(x_49);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec_ref(x_168);
x_82 = x_150;
x_83 = x_152;
x_84 = x_151;
x_85 = x_153;
x_86 = x_154;
x_87 = x_156;
x_88 = x_155;
x_89 = x_157;
x_90 = x_158;
x_91 = x_160;
x_92 = x_161;
x_93 = x_162;
x_94 = x_163;
x_95 = x_164;
x_96 = x_165;
x_97 = x_166;
x_98 = x_171;
goto block_149;
}
else
{
uint8_t x_172; 
x_172 = !lean_is_exclusive(x_168);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; size_t x_176; size_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_173 = lean_ctor_get(x_168, 1);
x_174 = lean_ctor_get(x_168, 0);
lean_dec(x_174);
x_175 = l_Lean_Meta_substCore___lam__2___closed__11;
x_176 = lean_array_size(x_157);
x_177 = 0;
lean_inc_ref(x_157);
x_178 = l_Array_mapMUnsafe_map___at___Lean_Meta_substCore_spec__11(x_176, x_177, x_157);
x_179 = lean_array_to_list(x_178);
x_180 = lean_box(0);
x_181 = l_List_mapTR_loop___at___Lean_Meta_substCore_spec__12(x_179, x_180);
x_182 = l_Lean_MessageData_ofList(x_181);
lean_ctor_set_tag(x_168, 7);
lean_ctor_set(x_168, 1, x_182);
lean_ctor_set(x_168, 0, x_175);
x_183 = l_Lean_Meta_substCore___lam__1___closed__4;
if (lean_is_scalar(x_49)) {
 x_184 = lean_alloc_ctor(7, 2, 0);
} else {
 x_184 = x_49;
 lean_ctor_set_tag(x_184, 7);
}
lean_ctor_set(x_184, 0, x_168);
lean_ctor_set(x_184, 1, x_183);
x_185 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4(x_159, x_184, x_163, x_164, x_165, x_166, x_173);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec_ref(x_185);
x_82 = x_150;
x_83 = x_152;
x_84 = x_151;
x_85 = x_153;
x_86 = x_154;
x_87 = x_156;
x_88 = x_155;
x_89 = x_157;
x_90 = x_158;
x_91 = x_160;
x_92 = x_161;
x_93 = x_162;
x_94 = x_163;
x_95 = x_164;
x_96 = x_165;
x_97 = x_166;
x_98 = x_186;
goto block_149;
}
else
{
lean_object* x_187; lean_object* x_188; size_t x_189; size_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_187 = lean_ctor_get(x_168, 1);
lean_inc(x_187);
lean_dec(x_168);
x_188 = l_Lean_Meta_substCore___lam__2___closed__11;
x_189 = lean_array_size(x_157);
x_190 = 0;
lean_inc_ref(x_157);
x_191 = l_Array_mapMUnsafe_map___at___Lean_Meta_substCore_spec__11(x_189, x_190, x_157);
x_192 = lean_array_to_list(x_191);
x_193 = lean_box(0);
x_194 = l_List_mapTR_loop___at___Lean_Meta_substCore_spec__12(x_192, x_193);
x_195 = l_Lean_MessageData_ofList(x_194);
x_196 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_196, 0, x_188);
lean_ctor_set(x_196, 1, x_195);
x_197 = l_Lean_Meta_substCore___lam__1___closed__4;
if (lean_is_scalar(x_49)) {
 x_198 = lean_alloc_ctor(7, 2, 0);
} else {
 x_198 = x_49;
 lean_ctor_set_tag(x_198, 7);
}
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4(x_159, x_198, x_163, x_164, x_165, x_166, x_187);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec_ref(x_199);
x_82 = x_150;
x_83 = x_152;
x_84 = x_151;
x_85 = x_153;
x_86 = x_154;
x_87 = x_156;
x_88 = x_155;
x_89 = x_157;
x_90 = x_158;
x_91 = x_160;
x_92 = x_161;
x_93 = x_162;
x_94 = x_163;
x_95 = x_164;
x_96 = x_165;
x_97 = x_166;
x_98 = x_200;
goto block_149;
}
}
}
block_262:
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_box(0);
lean_inc(x_215);
lean_inc_ref(x_214);
lean_inc(x_213);
lean_inc_ref(x_212);
lean_inc(x_209);
x_218 = l_Lean_Meta_introNCore(x_211, x_209, x_217, x_210, x_54, x_212, x_213, x_214, x_215, x_216);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec_ref(x_218);
x_221 = !lean_is_exclusive(x_219);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_222 = lean_ctor_get(x_219, 0);
x_223 = lean_ctor_get(x_219, 1);
lean_inc(x_208);
x_224 = l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3___redArg(x_208, x_214, x_220);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_unbox(x_225);
lean_dec(x_225);
if (x_226 == 0)
{
lean_object* x_227; 
lean_free_object(x_219);
x_227 = lean_ctor_get(x_224, 1);
lean_inc(x_227);
lean_dec_ref(x_224);
lean_inc(x_223);
x_150 = x_202;
x_151 = x_223;
x_152 = x_203;
x_153 = x_204;
x_154 = x_205;
x_155 = x_217;
x_156 = x_206;
x_157 = x_207;
x_158 = x_222;
x_159 = x_208;
x_160 = x_223;
x_161 = x_209;
x_162 = x_210;
x_163 = x_212;
x_164 = x_213;
x_165 = x_214;
x_166 = x_215;
x_167 = x_227;
goto block_201;
}
else
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_224);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_229 = lean_ctor_get(x_224, 1);
x_230 = lean_ctor_get(x_224, 0);
lean_dec(x_230);
x_231 = l_Lean_Meta_substCore___lam__2___closed__13;
lean_inc(x_223);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_223);
lean_ctor_set_tag(x_224, 7);
lean_ctor_set(x_224, 1, x_232);
lean_ctor_set(x_224, 0, x_231);
x_233 = l_Lean_Meta_substCore___lam__1___closed__4;
lean_ctor_set_tag(x_219, 7);
lean_ctor_set(x_219, 1, x_233);
lean_ctor_set(x_219, 0, x_224);
lean_inc(x_208);
x_234 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4(x_208, x_219, x_212, x_213, x_214, x_215, x_229);
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
lean_dec_ref(x_234);
lean_inc(x_223);
x_150 = x_202;
x_151 = x_223;
x_152 = x_203;
x_153 = x_204;
x_154 = x_205;
x_155 = x_217;
x_156 = x_206;
x_157 = x_207;
x_158 = x_222;
x_159 = x_208;
x_160 = x_223;
x_161 = x_209;
x_162 = x_210;
x_163 = x_212;
x_164 = x_213;
x_165 = x_214;
x_166 = x_215;
x_167 = x_235;
goto block_201;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_236 = lean_ctor_get(x_224, 1);
lean_inc(x_236);
lean_dec(x_224);
x_237 = l_Lean_Meta_substCore___lam__2___closed__13;
lean_inc(x_223);
x_238 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_238, 0, x_223);
x_239 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
x_240 = l_Lean_Meta_substCore___lam__1___closed__4;
lean_ctor_set_tag(x_219, 7);
lean_ctor_set(x_219, 1, x_240);
lean_ctor_set(x_219, 0, x_239);
lean_inc(x_208);
x_241 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4(x_208, x_219, x_212, x_213, x_214, x_215, x_236);
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec_ref(x_241);
lean_inc(x_223);
x_150 = x_202;
x_151 = x_223;
x_152 = x_203;
x_153 = x_204;
x_154 = x_205;
x_155 = x_217;
x_156 = x_206;
x_157 = x_207;
x_158 = x_222;
x_159 = x_208;
x_160 = x_223;
x_161 = x_209;
x_162 = x_210;
x_163 = x_212;
x_164 = x_213;
x_165 = x_214;
x_166 = x_215;
x_167 = x_242;
goto block_201;
}
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_243 = lean_ctor_get(x_219, 0);
x_244 = lean_ctor_get(x_219, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_219);
lean_inc(x_208);
x_245 = l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3___redArg(x_208, x_214, x_220);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_unbox(x_246);
lean_dec(x_246);
if (x_247 == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_245, 1);
lean_inc(x_248);
lean_dec_ref(x_245);
lean_inc(x_244);
x_150 = x_202;
x_151 = x_244;
x_152 = x_203;
x_153 = x_204;
x_154 = x_205;
x_155 = x_217;
x_156 = x_206;
x_157 = x_207;
x_158 = x_243;
x_159 = x_208;
x_160 = x_244;
x_161 = x_209;
x_162 = x_210;
x_163 = x_212;
x_164 = x_213;
x_165 = x_214;
x_166 = x_215;
x_167 = x_248;
goto block_201;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_249 = lean_ctor_get(x_245, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_250 = x_245;
} else {
 lean_dec_ref(x_245);
 x_250 = lean_box(0);
}
x_251 = l_Lean_Meta_substCore___lam__2___closed__13;
lean_inc(x_244);
x_252 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_252, 0, x_244);
if (lean_is_scalar(x_250)) {
 x_253 = lean_alloc_ctor(7, 2, 0);
} else {
 x_253 = x_250;
 lean_ctor_set_tag(x_253, 7);
}
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
x_254 = l_Lean_Meta_substCore___lam__1___closed__4;
x_255 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
lean_inc(x_208);
x_256 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4(x_208, x_255, x_212, x_213, x_214, x_215, x_249);
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
lean_dec_ref(x_256);
lean_inc(x_244);
x_150 = x_202;
x_151 = x_244;
x_152 = x_203;
x_153 = x_204;
x_154 = x_205;
x_155 = x_217;
x_156 = x_206;
x_157 = x_207;
x_158 = x_243;
x_159 = x_208;
x_160 = x_244;
x_161 = x_209;
x_162 = x_210;
x_163 = x_212;
x_164 = x_213;
x_165 = x_214;
x_166 = x_215;
x_167 = x_257;
goto block_201;
}
}
}
else
{
uint8_t x_258; 
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec_ref(x_212);
lean_dec(x_209);
lean_dec(x_208);
lean_dec_ref(x_207);
lean_dec(x_206);
lean_dec_ref(x_205);
lean_dec_ref(x_204);
lean_dec(x_202);
lean_dec(x_53);
lean_dec(x_49);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_258 = !lean_is_exclusive(x_218);
if (x_258 == 0)
{
return x_218;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_218, 0);
x_260 = lean_ctor_get(x_218, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_218);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
block_370:
{
lean_object* x_274; lean_object* x_275; uint8_t x_276; 
lean_inc_ref(x_265);
lean_inc_ref(x_268);
x_274 = l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg(x_268, x_265, x_270, x_273);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_unbox(x_275);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; lean_object* x_283; 
lean_dec_ref(x_268);
lean_dec_ref(x_267);
lean_dec(x_47);
x_277 = lean_ctor_get(x_274, 1);
lean_inc(x_277);
lean_dec_ref(x_274);
x_278 = lean_unsigned_to_nat(2u);
x_279 = l_Lean_Meta_substCore___lam__2___closed__14;
x_280 = lean_array_push(x_279, x_265);
lean_inc(x_2);
x_281 = lean_array_push(x_280, x_2);
x_282 = lean_unbox(x_275);
lean_inc(x_272);
lean_inc_ref(x_271);
lean_inc(x_270);
lean_inc_ref(x_269);
x_283 = l_Lean_MVarId_revert(x_1, x_281, x_54, x_282, x_269, x_270, x_271, x_272, x_277);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec_ref(x_283);
x_286 = !lean_is_exclusive(x_284);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_287 = lean_ctor_get(x_284, 0);
x_288 = lean_ctor_get(x_284, 1);
lean_inc(x_266);
x_289 = l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3___redArg(x_266, x_271, x_285);
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_unbox(x_290);
lean_dec(x_290);
if (x_291 == 0)
{
lean_object* x_292; uint8_t x_293; uint8_t x_294; 
lean_free_object(x_284);
x_292 = lean_ctor_get(x_289, 1);
lean_inc(x_292);
lean_dec_ref(x_289);
x_293 = lean_unbox(x_275);
x_294 = lean_unbox(x_275);
lean_dec(x_275);
lean_inc(x_287);
x_202 = x_263;
x_203 = x_293;
x_204 = x_287;
x_205 = x_264;
x_206 = x_278;
x_207 = x_287;
x_208 = x_266;
x_209 = x_278;
x_210 = x_294;
x_211 = x_288;
x_212 = x_269;
x_213 = x_270;
x_214 = x_271;
x_215 = x_272;
x_216 = x_292;
goto block_262;
}
else
{
uint8_t x_295; 
x_295 = !lean_is_exclusive(x_289);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; uint8_t x_304; 
x_296 = lean_ctor_get(x_289, 1);
x_297 = lean_ctor_get(x_289, 0);
lean_dec(x_297);
x_298 = l_Lean_Meta_substCore___lam__2___closed__16;
lean_inc(x_288);
x_299 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_299, 0, x_288);
lean_ctor_set_tag(x_289, 7);
lean_ctor_set(x_289, 1, x_299);
lean_ctor_set(x_289, 0, x_298);
x_300 = l_Lean_Meta_substCore___lam__1___closed__4;
lean_ctor_set_tag(x_284, 7);
lean_ctor_set(x_284, 1, x_300);
lean_ctor_set(x_284, 0, x_289);
lean_inc(x_266);
x_301 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4(x_266, x_284, x_269, x_270, x_271, x_272, x_296);
x_302 = lean_ctor_get(x_301, 1);
lean_inc(x_302);
lean_dec_ref(x_301);
x_303 = lean_unbox(x_275);
x_304 = lean_unbox(x_275);
lean_dec(x_275);
lean_inc(x_287);
x_202 = x_263;
x_203 = x_303;
x_204 = x_287;
x_205 = x_264;
x_206 = x_278;
x_207 = x_287;
x_208 = x_266;
x_209 = x_278;
x_210 = x_304;
x_211 = x_288;
x_212 = x_269;
x_213 = x_270;
x_214 = x_271;
x_215 = x_272;
x_216 = x_302;
goto block_262;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; uint8_t x_313; 
x_305 = lean_ctor_get(x_289, 1);
lean_inc(x_305);
lean_dec(x_289);
x_306 = l_Lean_Meta_substCore___lam__2___closed__16;
lean_inc(x_288);
x_307 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_307, 0, x_288);
x_308 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
x_309 = l_Lean_Meta_substCore___lam__1___closed__4;
lean_ctor_set_tag(x_284, 7);
lean_ctor_set(x_284, 1, x_309);
lean_ctor_set(x_284, 0, x_308);
lean_inc(x_266);
x_310 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4(x_266, x_284, x_269, x_270, x_271, x_272, x_305);
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
lean_dec_ref(x_310);
x_312 = lean_unbox(x_275);
x_313 = lean_unbox(x_275);
lean_dec(x_275);
lean_inc(x_287);
x_202 = x_263;
x_203 = x_312;
x_204 = x_287;
x_205 = x_264;
x_206 = x_278;
x_207 = x_287;
x_208 = x_266;
x_209 = x_278;
x_210 = x_313;
x_211 = x_288;
x_212 = x_269;
x_213 = x_270;
x_214 = x_271;
x_215 = x_272;
x_216 = x_311;
goto block_262;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_314 = lean_ctor_get(x_284, 0);
x_315 = lean_ctor_get(x_284, 1);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_284);
lean_inc(x_266);
x_316 = l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3___redArg(x_266, x_271, x_285);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_unbox(x_317);
lean_dec(x_317);
if (x_318 == 0)
{
lean_object* x_319; uint8_t x_320; uint8_t x_321; 
x_319 = lean_ctor_get(x_316, 1);
lean_inc(x_319);
lean_dec_ref(x_316);
x_320 = lean_unbox(x_275);
x_321 = lean_unbox(x_275);
lean_dec(x_275);
lean_inc(x_314);
x_202 = x_263;
x_203 = x_320;
x_204 = x_314;
x_205 = x_264;
x_206 = x_278;
x_207 = x_314;
x_208 = x_266;
x_209 = x_278;
x_210 = x_321;
x_211 = x_315;
x_212 = x_269;
x_213 = x_270;
x_214 = x_271;
x_215 = x_272;
x_216 = x_319;
goto block_262;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; uint8_t x_332; 
x_322 = lean_ctor_get(x_316, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_323 = x_316;
} else {
 lean_dec_ref(x_316);
 x_323 = lean_box(0);
}
x_324 = l_Lean_Meta_substCore___lam__2___closed__16;
lean_inc(x_315);
x_325 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_325, 0, x_315);
if (lean_is_scalar(x_323)) {
 x_326 = lean_alloc_ctor(7, 2, 0);
} else {
 x_326 = x_323;
 lean_ctor_set_tag(x_326, 7);
}
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
x_327 = l_Lean_Meta_substCore___lam__1___closed__4;
x_328 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
lean_inc(x_266);
x_329 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4(x_266, x_328, x_269, x_270, x_271, x_272, x_322);
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
lean_dec_ref(x_329);
x_331 = lean_unbox(x_275);
x_332 = lean_unbox(x_275);
lean_dec(x_275);
lean_inc(x_314);
x_202 = x_263;
x_203 = x_331;
x_204 = x_314;
x_205 = x_264;
x_206 = x_278;
x_207 = x_314;
x_208 = x_266;
x_209 = x_278;
x_210 = x_332;
x_211 = x_315;
x_212 = x_269;
x_213 = x_270;
x_214 = x_271;
x_215 = x_272;
x_216 = x_330;
goto block_262;
}
}
}
else
{
uint8_t x_333; 
lean_dec(x_275);
lean_dec(x_272);
lean_dec_ref(x_271);
lean_dec(x_270);
lean_dec_ref(x_269);
lean_dec(x_266);
lean_dec_ref(x_264);
lean_dec(x_263);
lean_dec(x_53);
lean_dec(x_49);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_333 = !lean_is_exclusive(x_283);
if (x_333 == 0)
{
return x_283;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_283, 0);
x_335 = lean_ctor_get(x_283, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_283);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
}
else
{
uint8_t x_337; 
lean_dec(x_275);
lean_dec(x_266);
lean_dec_ref(x_265);
lean_dec_ref(x_264);
lean_dec(x_263);
lean_dec(x_53);
lean_dec(x_49);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_337 = !lean_is_exclusive(x_274);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; 
x_338 = lean_ctor_get(x_274, 1);
x_339 = lean_ctor_get(x_274, 0);
lean_dec(x_339);
x_340 = l_Lean_Meta_substCore___lam__2___closed__18;
x_341 = l_Lean_MessageData_ofExpr(x_267);
lean_ctor_set_tag(x_274, 7);
lean_ctor_set(x_274, 1, x_341);
lean_ctor_set(x_274, 0, x_340);
x_342 = l_Lean_Meta_substCore___lam__2___closed__20;
x_343 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_343, 0, x_274);
lean_ctor_set(x_343, 1, x_342);
x_344 = l_Lean_indentExpr(x_268);
x_345 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
x_346 = l_Lean_Meta_substCore___lam__1___closed__4;
x_347 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
if (lean_is_scalar(x_47)) {
 x_348 = lean_alloc_ctor(1, 1, 0);
} else {
 x_348 = x_47;
}
lean_ctor_set(x_348, 0, x_347);
x_349 = l_Lean_Meta_throwTacticEx___redArg(x_16, x_1, x_348, x_269, x_270, x_271, x_272, x_338);
lean_dec(x_272);
lean_dec_ref(x_271);
lean_dec(x_270);
lean_dec_ref(x_269);
x_350 = !lean_is_exclusive(x_349);
if (x_350 == 0)
{
return x_349;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_349, 0);
x_352 = lean_ctor_get(x_349, 1);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_349);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
return x_353;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_354 = lean_ctor_get(x_274, 1);
lean_inc(x_354);
lean_dec(x_274);
x_355 = l_Lean_Meta_substCore___lam__2___closed__18;
x_356 = l_Lean_MessageData_ofExpr(x_267);
x_357 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
x_358 = l_Lean_Meta_substCore___lam__2___closed__20;
x_359 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set(x_359, 1, x_358);
x_360 = l_Lean_indentExpr(x_268);
x_361 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_360);
x_362 = l_Lean_Meta_substCore___lam__1___closed__4;
x_363 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_362);
if (lean_is_scalar(x_47)) {
 x_364 = lean_alloc_ctor(1, 1, 0);
} else {
 x_364 = x_47;
}
lean_ctor_set(x_364, 0, x_363);
x_365 = l_Lean_Meta_throwTacticEx___redArg(x_16, x_1, x_364, x_269, x_270, x_271, x_272, x_354);
lean_dec(x_272);
lean_dec_ref(x_271);
lean_dec(x_270);
lean_dec_ref(x_269);
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_368 = x_365;
} else {
 lean_dec_ref(x_365);
 x_368 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_369 = lean_alloc_ctor(1, 2, 0);
} else {
 x_369 = x_368;
}
lean_ctor_set(x_369, 0, x_366);
lean_ctor_set(x_369, 1, x_367);
return x_369;
}
}
}
block_444:
{
lean_object* x_374; 
x_374 = l_Lean_instantiateMVars___at___Lean_Meta_substCore_spec__0___redArg(x_373, x_9, x_371);
if (lean_obj_tag(x_372) == 1)
{
uint8_t x_375; 
lean_dec_ref(x_22);
x_375 = !lean_is_exclusive(x_374);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; 
x_376 = lean_ctor_get(x_374, 0);
x_377 = lean_ctor_get(x_374, 1);
x_378 = lean_ctor_get(x_372, 0);
lean_inc(x_378);
x_379 = l_Lean_Meta_substCore___lam__2___closed__23;
x_380 = l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3___redArg(x_379, x_10, x_377);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_unbox(x_381);
lean_dec(x_381);
if (x_382 == 0)
{
lean_object* x_383; 
lean_free_object(x_374);
x_383 = lean_ctor_get(x_380, 1);
lean_inc(x_383);
lean_dec_ref(x_380);
lean_inc(x_378);
x_263 = x_379;
x_264 = x_378;
x_265 = x_378;
x_266 = x_379;
x_267 = x_372;
x_268 = x_376;
x_269 = x_8;
x_270 = x_9;
x_271 = x_10;
x_272 = x_11;
x_273 = x_383;
goto block_370;
}
else
{
uint8_t x_384; 
x_384 = !lean_is_exclusive(x_380);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_385 = lean_ctor_get(x_380, 1);
x_386 = lean_ctor_get(x_380, 0);
lean_dec(x_386);
x_387 = l_Lean_Meta_substCore___lam__2___closed__25;
lean_inc_ref(x_372);
x_388 = l_Lean_MessageData_ofExpr(x_372);
lean_ctor_set_tag(x_380, 7);
lean_ctor_set(x_380, 1, x_388);
lean_ctor_set(x_380, 0, x_387);
x_389 = l_Lean_Meta_substCore___lam__2___closed__27;
lean_ctor_set_tag(x_374, 7);
lean_ctor_set(x_374, 1, x_389);
lean_ctor_set(x_374, 0, x_380);
lean_inc(x_378);
x_390 = l_Lean_MessageData_ofName(x_378);
x_391 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_391, 0, x_374);
lean_ctor_set(x_391, 1, x_390);
x_392 = l_Lean_Meta_substCore___lam__2___closed__29;
x_393 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
lean_inc(x_376);
x_394 = l_Lean_MessageData_ofExpr(x_376);
x_395 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
x_396 = l_Lean_Meta_substCore___lam__1___closed__4;
x_397 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_397, 0, x_395);
lean_ctor_set(x_397, 1, x_396);
x_398 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4(x_379, x_397, x_8, x_9, x_10, x_11, x_385);
x_399 = lean_ctor_get(x_398, 1);
lean_inc(x_399);
lean_dec_ref(x_398);
lean_inc(x_378);
x_263 = x_379;
x_264 = x_378;
x_265 = x_378;
x_266 = x_379;
x_267 = x_372;
x_268 = x_376;
x_269 = x_8;
x_270 = x_9;
x_271 = x_10;
x_272 = x_11;
x_273 = x_399;
goto block_370;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_400 = lean_ctor_get(x_380, 1);
lean_inc(x_400);
lean_dec(x_380);
x_401 = l_Lean_Meta_substCore___lam__2___closed__25;
lean_inc_ref(x_372);
x_402 = l_Lean_MessageData_ofExpr(x_372);
x_403 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_402);
x_404 = l_Lean_Meta_substCore___lam__2___closed__27;
lean_ctor_set_tag(x_374, 7);
lean_ctor_set(x_374, 1, x_404);
lean_ctor_set(x_374, 0, x_403);
lean_inc(x_378);
x_405 = l_Lean_MessageData_ofName(x_378);
x_406 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_406, 0, x_374);
lean_ctor_set(x_406, 1, x_405);
x_407 = l_Lean_Meta_substCore___lam__2___closed__29;
x_408 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
lean_inc(x_376);
x_409 = l_Lean_MessageData_ofExpr(x_376);
x_410 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
x_411 = l_Lean_Meta_substCore___lam__1___closed__4;
x_412 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
x_413 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4(x_379, x_412, x_8, x_9, x_10, x_11, x_400);
x_414 = lean_ctor_get(x_413, 1);
lean_inc(x_414);
lean_dec_ref(x_413);
lean_inc(x_378);
x_263 = x_379;
x_264 = x_378;
x_265 = x_378;
x_266 = x_379;
x_267 = x_372;
x_268 = x_376;
x_269 = x_8;
x_270 = x_9;
x_271 = x_10;
x_272 = x_11;
x_273 = x_414;
goto block_370;
}
}
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; 
x_415 = lean_ctor_get(x_374, 0);
x_416 = lean_ctor_get(x_374, 1);
lean_inc(x_416);
lean_inc(x_415);
lean_dec(x_374);
x_417 = lean_ctor_get(x_372, 0);
lean_inc(x_417);
x_418 = l_Lean_Meta_substCore___lam__2___closed__23;
x_419 = l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3___redArg(x_418, x_10, x_416);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_unbox(x_420);
lean_dec(x_420);
if (x_421 == 0)
{
lean_object* x_422; 
x_422 = lean_ctor_get(x_419, 1);
lean_inc(x_422);
lean_dec_ref(x_419);
lean_inc(x_417);
x_263 = x_418;
x_264 = x_417;
x_265 = x_417;
x_266 = x_418;
x_267 = x_372;
x_268 = x_415;
x_269 = x_8;
x_270 = x_9;
x_271 = x_10;
x_272 = x_11;
x_273 = x_422;
goto block_370;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_423 = lean_ctor_get(x_419, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 x_424 = x_419;
} else {
 lean_dec_ref(x_419);
 x_424 = lean_box(0);
}
x_425 = l_Lean_Meta_substCore___lam__2___closed__25;
lean_inc_ref(x_372);
x_426 = l_Lean_MessageData_ofExpr(x_372);
if (lean_is_scalar(x_424)) {
 x_427 = lean_alloc_ctor(7, 2, 0);
} else {
 x_427 = x_424;
 lean_ctor_set_tag(x_427, 7);
}
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set(x_427, 1, x_426);
x_428 = l_Lean_Meta_substCore___lam__2___closed__27;
x_429 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
lean_inc(x_417);
x_430 = l_Lean_MessageData_ofName(x_417);
x_431 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_431, 0, x_429);
lean_ctor_set(x_431, 1, x_430);
x_432 = l_Lean_Meta_substCore___lam__2___closed__29;
x_433 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
lean_inc(x_415);
x_434 = l_Lean_MessageData_ofExpr(x_415);
x_435 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_435, 0, x_433);
lean_ctor_set(x_435, 1, x_434);
x_436 = l_Lean_Meta_substCore___lam__1___closed__4;
x_437 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
x_438 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4(x_418, x_437, x_8, x_9, x_10, x_11, x_423);
x_439 = lean_ctor_get(x_438, 1);
lean_inc(x_439);
lean_dec_ref(x_438);
lean_inc(x_417);
x_263 = x_418;
x_264 = x_417;
x_265 = x_417;
x_266 = x_418;
x_267 = x_372;
x_268 = x_415;
x_269 = x_8;
x_270 = x_9;
x_271 = x_10;
x_272 = x_11;
x_273 = x_439;
goto block_370;
}
}
}
else
{
lean_dec(x_53);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
if (x_6 == 0)
{
lean_object* x_440; lean_object* x_441; 
x_440 = lean_ctor_get(x_374, 1);
lean_inc(x_440);
lean_dec_ref(x_374);
x_441 = l_Lean_Meta_substCore___lam__2___closed__30;
x_23 = x_440;
x_24 = x_372;
x_25 = x_441;
goto block_40;
}
else
{
lean_object* x_442; lean_object* x_443; 
x_442 = lean_ctor_get(x_374, 1);
lean_inc(x_442);
lean_dec_ref(x_374);
x_443 = l_Lean_Meta_substCore___lam__2___closed__31;
x_23 = x_442;
x_24 = x_372;
x_25 = x_443;
goto block_40;
}
}
}
block_451:
{
lean_object* x_446; 
x_446 = l_Lean_instantiateMVars___at___Lean_Meta_substCore_spec__0___redArg(x_445, x_9, x_50);
if (x_6 == 0)
{
lean_object* x_447; lean_object* x_448; 
lean_dec(x_51);
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_446, 1);
lean_inc(x_448);
lean_dec_ref(x_446);
x_371 = x_448;
x_372 = x_447;
x_373 = x_52;
goto block_444;
}
else
{
lean_object* x_449; lean_object* x_450; 
lean_dec(x_52);
x_449 = lean_ctor_get(x_446, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_446, 1);
lean_inc(x_450);
lean_dec_ref(x_446);
x_371 = x_450;
x_372 = x_449;
x_373 = x_51;
goto block_444;
}
}
}
}
else
{
uint8_t x_452; 
lean_dec_ref(x_22);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_452 = !lean_is_exclusive(x_41);
if (x_452 == 0)
{
return x_41;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_41, 0);
x_454 = lean_ctor_get(x_41, 1);
lean_inc(x_454);
lean_inc(x_453);
lean_dec(x_41);
x_455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_455, 0, x_453);
lean_ctor_set(x_455, 1, x_454);
return x_455;
}
}
block_40:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_26 = l_Lean_Meta_substCore___lam__2___closed__3;
x_27 = l_Lean_stringToMessageData(x_25);
lean_dec_ref(x_25);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Meta_substCore___lam__1___closed__4;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_indentExpr(x_22);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Meta_substCore___lam__2___closed__5;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_indentExpr(x_24);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_29);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_Meta_throwTacticEx___redArg(x_16, x_1, x_38, x_8, x_9, x_10, x_11, x_23);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_39;
}
}
else
{
uint8_t x_456; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_456 = !lean_is_exclusive(x_19);
if (x_456 == 0)
{
return x_19;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_19, 0);
x_458 = lean_ctor_get(x_19, 1);
lean_inc(x_458);
lean_inc(x_457);
lean_dec(x_19);
x_459 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_459, 0, x_457);
lean_ctor_set(x_459, 1, x_458);
return x_459;
}
}
}
else
{
uint8_t x_460; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_460 = !lean_is_exclusive(x_17);
if (x_460 == 0)
{
return x_17;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_461 = lean_ctor_get(x_17, 0);
x_462 = lean_ctor_get(x_17, 1);
lean_inc(x_462);
lean_inc(x_461);
lean_dec(x_17);
x_463 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_463, 0, x_461);
lean_ctor_set(x_463, 1, x_462);
return x_463;
}
}
}
else
{
uint8_t x_464; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_464 = !lean_is_exclusive(x_13);
if (x_464 == 0)
{
return x_13;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_465 = lean_ctor_get(x_13, 0);
x_466 = lean_ctor_get(x_13, 1);
lean_inc(x_466);
lean_inc(x_465);
lean_dec(x_13);
x_467 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_467, 0, x_465);
lean_ctor_set(x_467, 1, x_466);
return x_467;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_box(0);
x_13 = lean_box(x_5);
x_14 = lean_box(x_3);
x_15 = lean_box(x_6);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__2___boxed), 12, 7);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_12);
lean_closure_set(x_16, 3, x_13);
lean_closure_set(x_16, 4, x_4);
lean_closure_set(x_16, 5, x_14);
lean_closure_set(x_16, 6, x_15);
x_17 = l_Lean_MVarId_withContext___at___Lean_Meta_substCore_spec__10___redArg(x_1, x_16, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_substCore_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___Lean_Meta_substCore_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_substCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___Lean_Meta_substCore_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_Meta_substCore_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldM_loop___at___Lean_Meta_substCore_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_Meta_substCore_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Nat_foldM_loop___at___Lean_Meta_substCore_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___Lean_Meta_substCore_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_substCore_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_substCore_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Meta_substCore_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8_spec__8___redArg(x_1, x_11, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_substCore_spec__8_spec__8(x_1, x_2, x_12, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_substCore_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Meta_substCore_spec__11(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_5);
x_14 = lean_unbox(x_6);
x_15 = l_Lean_Meta_substCore___lam__0(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
_start:
{
uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; 
x_26 = lean_unbox(x_10);
x_27 = lean_unbox(x_13);
x_28 = lean_unbox(x_14);
x_29 = lean_unbox(x_18);
x_30 = lean_unbox(x_19);
x_31 = l_Lean_Meta_substCore___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26, x_11, x_12, x_27, x_28, x_15, x_16, x_17, x_29, x_30, x_20, x_21, x_22, x_23, x_24, x_25);
lean_dec(x_20);
lean_dec_ref(x_8);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_4);
x_14 = lean_unbox(x_6);
x_15 = lean_unbox(x_7);
x_16 = l_Lean_Meta_substCore___lam__2(x_1, x_2, x_3, x_13, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_5);
x_14 = lean_unbox(x_6);
x_15 = l_Lean_Meta_substCore(x_1, x_2, x_12, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_heqToEq___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEq", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_heqToEq___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_heqToEq___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_4);
lean_inc(x_1);
x_9 = l_Lean_FVarId_getDecl___redArg(x_1, x_4, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Lean_LocalDecl_type(x_10);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_13 = lean_whnf(x_12, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Meta_heqToEq___lam__0___closed__1;
x_18 = lean_unsigned_to_nat(4u);
x_19 = l_Lean_Expr_isAppOfArity(x_15, x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_13);
x_21 = l_Lean_Expr_appFn_x21(x_15);
x_22 = l_Lean_Expr_appFn_x21(x_21);
x_23 = l_Lean_Expr_appFn_x21(x_22);
x_24 = l_Lean_Expr_appArg_x21(x_23);
lean_dec_ref(x_23);
x_25 = l_Lean_Expr_appArg_x21(x_21);
lean_dec_ref(x_21);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_26 = l_Lean_Meta_isExprDefEq(x_24, x_25, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_27);
lean_dec_ref(x_22);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_2);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec_ref(x_26);
lean_inc(x_1);
x_36 = l_Lean_mkFVar(x_1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_37 = l_Lean_Meta_mkEqOfHEq(x_36, x_19, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
x_40 = l_Lean_Expr_appArg_x21(x_22);
lean_dec_ref(x_22);
x_41 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_42 = l_Lean_Meta_mkEq(x_40, x_41, x_4, x_5, x_6, x_7, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = l_Lean_LocalDecl_userName(x_10);
lean_dec(x_10);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_46 = l_Lean_MVarId_assert(x_2, x_45, x_43, x_38, x_4, x_5, x_6, x_7, x_44);
if (lean_obj_tag(x_46) == 0)
{
if (x_3 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
lean_dec(x_1);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_unbox(x_27);
lean_dec(x_27);
x_50 = l_Lean_Meta_intro1Core(x_47, x_49, x_4, x_5, x_6, x_7, x_48);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec_ref(x_46);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_53 = l_Lean_MVarId_tryClear(x_51, x_1, x_4, x_5, x_6, x_7, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = lean_unbox(x_27);
lean_dec(x_27);
x_57 = l_Lean_Meta_intro1Core(x_54, x_56, x_4, x_5, x_6, x_7, x_55);
return x_57;
}
else
{
uint8_t x_58; 
lean_dec(x_27);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_58 = !lean_is_exclusive(x_53);
if (x_58 == 0)
{
return x_53;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_53, 0);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_53);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_27);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_46);
if (x_62 == 0)
{
return x_46;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_46, 0);
x_64 = lean_ctor_get(x_46, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_46);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_38);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_42);
if (x_66 == 0)
{
return x_42;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_42, 0);
x_68 = lean_ctor_get(x_42, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_42);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_27);
lean_dec_ref(x_22);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_37);
if (x_70 == 0)
{
return x_37;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_37, 0);
x_72 = lean_ctor_get(x_37, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_37);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
uint8_t x_74; 
lean_dec_ref(x_22);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_26);
if (x_74 == 0)
{
return x_26;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_26, 0);
x_76 = lean_ctor_get(x_26, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_26);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_78 = lean_ctor_get(x_13, 0);
x_79 = lean_ctor_get(x_13, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_13);
x_80 = l_Lean_Meta_heqToEq___lam__0___closed__1;
x_81 = lean_unsigned_to_nat(4u);
x_82 = l_Lean_Expr_isAppOfArity(x_78, x_80, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_78);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_2);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_79);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = l_Lean_Expr_appFn_x21(x_78);
x_86 = l_Lean_Expr_appFn_x21(x_85);
x_87 = l_Lean_Expr_appFn_x21(x_86);
x_88 = l_Lean_Expr_appArg_x21(x_87);
lean_dec_ref(x_87);
x_89 = l_Lean_Expr_appArg_x21(x_85);
lean_dec_ref(x_85);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_90 = l_Lean_Meta_isExprDefEq(x_88, x_89, x_4, x_5, x_6, x_7, x_79);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_unbox(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_91);
lean_dec_ref(x_86);
lean_dec(x_78);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_94 = x_90;
} else {
 lean_dec_ref(x_90);
 x_94 = lean_box(0);
}
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_2);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_90, 1);
lean_inc(x_97);
lean_dec_ref(x_90);
lean_inc(x_1);
x_98 = l_Lean_mkFVar(x_1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_99 = l_Lean_Meta_mkEqOfHEq(x_98, x_82, x_4, x_5, x_6, x_7, x_97);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec_ref(x_99);
x_102 = l_Lean_Expr_appArg_x21(x_86);
lean_dec_ref(x_86);
x_103 = l_Lean_Expr_appArg_x21(x_78);
lean_dec(x_78);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_104 = l_Lean_Meta_mkEq(x_102, x_103, x_4, x_5, x_6, x_7, x_101);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec_ref(x_104);
x_107 = l_Lean_LocalDecl_userName(x_10);
lean_dec(x_10);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_108 = l_Lean_MVarId_assert(x_2, x_107, x_105, x_100, x_4, x_5, x_6, x_7, x_106);
if (lean_obj_tag(x_108) == 0)
{
if (x_3 == 0)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; 
lean_dec(x_1);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec_ref(x_108);
x_111 = lean_unbox(x_91);
lean_dec(x_91);
x_112 = l_Lean_Meta_intro1Core(x_109, x_111, x_4, x_5, x_6, x_7, x_110);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_108, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
lean_dec_ref(x_108);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_115 = l_Lean_MVarId_tryClear(x_113, x_1, x_4, x_5, x_6, x_7, x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec_ref(x_115);
x_118 = lean_unbox(x_91);
lean_dec(x_91);
x_119 = l_Lean_Meta_intro1Core(x_116, x_118, x_4, x_5, x_6, x_7, x_117);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_91);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_120 = lean_ctor_get(x_115, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_115, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_122 = x_115;
} else {
 lean_dec_ref(x_115);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_91);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_124 = lean_ctor_get(x_108, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_108, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_126 = x_108;
} else {
 lean_dec_ref(x_108);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_100);
lean_dec(x_91);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_128 = lean_ctor_get(x_104, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_104, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_130 = x_104;
} else {
 lean_dec_ref(x_104);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_91);
lean_dec_ref(x_86);
lean_dec(x_78);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_132 = lean_ctor_get(x_99, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_99, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_134 = x_99;
} else {
 lean_dec_ref(x_99);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec_ref(x_86);
lean_dec(x_78);
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_136 = lean_ctor_get(x_90, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_90, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_138 = x_90;
} else {
 lean_dec_ref(x_90);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_13);
if (x_140 == 0)
{
return x_13;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_13, 0);
x_142 = lean_ctor_get(x_13, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_13);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_144 = !lean_is_exclusive(x_9);
if (x_144 == 0)
{
return x_9;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_9, 0);
x_146 = lean_ctor_get(x_9, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_9);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(x_3);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_heqToEq___lam__0___boxed), 8, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_9);
x_11 = l_Lean_MVarId_withContext___at___Lean_Meta_substCore_spec__10___redArg(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_heqToEq___lam__0(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_heqToEq(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_7);
x_15 = lean_array_uget(x_4, x_6);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_1);
x_16 = l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0(x_1, x_15, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; size_t x_19; size_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_6, x_19);
lean_inc_ref(x_2);
{
size_t _tmp_5 = x_20;
lean_object* _tmp_6 = x_2;
lean_object* _tmp_11 = x_18;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_12 = _tmp_11;
}
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
lean_dec(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_17);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_17);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_7);
x_15 = lean_array_uget(x_4, x_6);
lean_inc_ref(x_1);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_16 = lean_apply_6(x_1, x_15, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; size_t x_19; size_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_6, x_19);
lean_inc_ref(x_2);
{
size_t _tmp_5 = x_20;
lean_object* _tmp_6 = x_2;
lean_object* _tmp_11 = x_18;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_12 = _tmp_11;
}
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
lean_dec(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_17);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_17);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_15 = x_2;
} else {
 lean_dec_ref(x_2);
 x_15 = lean_box(0);
}
x_16 = l_Lean_LocalDecl_isImplementationDetail(x_14);
if (x_16 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_LocalDecl_type(x_14);
lean_inc(x_4);
x_25 = l_Lean_Meta_matchEq_x3f(x_24, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_57; lean_object* x_58; uint8_t x_63; lean_object* x_64; uint8_t x_71; uint8_t x_79; 
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_34 = x_26;
} else {
 lean_dec_ref(x_26);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_dec_ref(x_25);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_39 = x_35;
} else {
 lean_dec_ref(x_35);
 x_39 = lean_box(0);
}
x_40 = l_Lean_instantiateMVars___at___Lean_Meta_substCore_spec__0___redArg(x_37, x_4, x_36);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = l_Lean_instantiateMVars___at___Lean_Meta_substCore_spec__0___redArg(x_38, x_4, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_63 = 1;
x_79 = l_Lean_Expr_isFVar(x_44);
if (x_79 == 0)
{
x_71 = x_79;
goto block_78;
}
else
{
lean_object* x_80; uint8_t x_81; 
x_80 = l_Lean_Expr_fvarId_x21(x_44);
x_81 = l_Lean_beqFVarId____x40_Lean_Expr___hyg_1504_(x_80, x_1);
lean_dec(x_80);
x_71 = x_81;
goto block_78;
}
block_56:
{
if (x_49 == 0)
{
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_8 = x_48;
goto block_11;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg(x_44, x_1, x_47, x_48);
lean_dec(x_47);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec_ref(x_50);
x_17 = x_53;
goto block_23;
}
else
{
if (x_16 == 0)
{
lean_object* x_54; 
lean_dec(x_15);
lean_dec(x_14);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec_ref(x_50);
x_8 = x_54;
goto block_11;
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_dec_ref(x_50);
x_17 = x_55;
goto block_23;
}
}
}
}
block_62:
{
uint8_t x_59; 
x_59 = l_Lean_Expr_isFVar(x_41);
if (x_59 == 0)
{
lean_dec(x_41);
x_47 = x_57;
x_48 = x_58;
x_49 = x_59;
goto block_56;
}
else
{
lean_object* x_60; uint8_t x_61; 
x_60 = l_Lean_Expr_fvarId_x21(x_41);
lean_dec(x_41);
x_61 = l_Lean_beqFVarId____x40_Lean_Expr___hyg_1504_(x_60, x_1);
lean_dec(x_60);
x_47 = x_57;
x_48 = x_58;
x_49 = x_61;
goto block_56;
}
}
block_70:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_66 = lean_box(x_63);
if (lean_is_scalar(x_39)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_39;
}
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
if (lean_is_scalar(x_34)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_34;
}
lean_ctor_set(x_68, 0, x_67);
if (lean_is_scalar(x_46)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_46;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_64);
return x_69;
}
block_78:
{
if (x_71 == 0)
{
lean_dec(x_46);
lean_dec(x_39);
lean_dec(x_34);
x_57 = x_4;
x_58 = x_45;
goto block_62;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_inc(x_1);
lean_inc(x_41);
x_72 = l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg(x_41, x_1, x_4, x_45);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_1);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec_ref(x_72);
x_64 = x_75;
goto block_70;
}
else
{
if (x_16 == 0)
{
lean_object* x_76; 
lean_dec(x_46);
lean_dec(x_39);
lean_dec(x_34);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec_ref(x_72);
x_57 = x_4;
x_58 = x_76;
goto block_62;
}
else
{
lean_object* x_77; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_1);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_dec_ref(x_72);
x_64 = x_77;
goto block_70;
}
}
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_25);
if (x_82 == 0)
{
return x_25;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_25, 0);
x_84 = lean_ctor_get(x_25, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_25);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_7);
return x_87;
}
block_23:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_19 = lean_box(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
if (lean_is_scalar(x_15)) {
 x_21 = lean_alloc_ctor(1, 1, 0);
} else {
 x_21 = x_15;
}
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
static lean_object* _init_l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_box(0);
x_10 = l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0___closed__0;
x_11 = lean_array_size(x_8);
x_12 = 0;
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0_spec__0(x_1, x_10, x_9, x_8, x_11, x_12, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_13, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec_ref(x_15);
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec_ref(x_15);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0___lam__0), 7, 1);
lean_closure_set(x_33, 0, x_1);
x_34 = lean_box(0);
x_35 = l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0___closed__0;
x_36 = lean_array_size(x_32);
x_37 = 0;
x_38 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0_spec__1(x_33, x_35, x_34, x_32, x_36, x_37, x_35, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_38);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_38, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
lean_dec_ref(x_40);
lean_ctor_set(x_38, 0, x_49);
return x_38;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_dec(x_38);
x_51 = lean_ctor_get(x_40, 0);
lean_inc(x_51);
lean_dec_ref(x_40);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_38);
if (x_53 == 0)
{
return x_38;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_38, 0);
x_55 = lean_ctor_get(x_38, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_38);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_15 = x_2;
} else {
 lean_dec_ref(x_2);
 x_15 = lean_box(0);
}
x_16 = l_Lean_LocalDecl_isImplementationDetail(x_14);
if (x_16 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_LocalDecl_type(x_14);
lean_inc(x_4);
x_25 = l_Lean_Meta_matchEq_x3f(x_24, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_57; lean_object* x_58; uint8_t x_63; lean_object* x_64; uint8_t x_71; uint8_t x_79; 
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_34 = x_26;
} else {
 lean_dec_ref(x_26);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_dec_ref(x_25);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_39 = x_35;
} else {
 lean_dec_ref(x_35);
 x_39 = lean_box(0);
}
x_40 = l_Lean_instantiateMVars___at___Lean_Meta_substCore_spec__0___redArg(x_37, x_4, x_36);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = l_Lean_instantiateMVars___at___Lean_Meta_substCore_spec__0___redArg(x_38, x_4, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_63 = 1;
x_79 = l_Lean_Expr_isFVar(x_44);
if (x_79 == 0)
{
x_71 = x_79;
goto block_78;
}
else
{
lean_object* x_80; uint8_t x_81; 
x_80 = l_Lean_Expr_fvarId_x21(x_44);
x_81 = l_Lean_beqFVarId____x40_Lean_Expr___hyg_1504_(x_80, x_1);
lean_dec(x_80);
x_71 = x_81;
goto block_78;
}
block_56:
{
if (x_49 == 0)
{
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_8 = x_48;
goto block_11;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg(x_44, x_1, x_47, x_48);
lean_dec(x_47);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec_ref(x_50);
x_17 = x_53;
goto block_23;
}
else
{
if (x_16 == 0)
{
lean_object* x_54; 
lean_dec(x_15);
lean_dec(x_14);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec_ref(x_50);
x_8 = x_54;
goto block_11;
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_dec_ref(x_50);
x_17 = x_55;
goto block_23;
}
}
}
}
block_62:
{
uint8_t x_59; 
x_59 = l_Lean_Expr_isFVar(x_41);
if (x_59 == 0)
{
lean_dec(x_41);
x_47 = x_57;
x_48 = x_58;
x_49 = x_59;
goto block_56;
}
else
{
lean_object* x_60; uint8_t x_61; 
x_60 = l_Lean_Expr_fvarId_x21(x_41);
lean_dec(x_41);
x_61 = l_Lean_beqFVarId____x40_Lean_Expr___hyg_1504_(x_60, x_1);
lean_dec(x_60);
x_47 = x_57;
x_48 = x_58;
x_49 = x_61;
goto block_56;
}
}
block_70:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_66 = lean_box(x_63);
if (lean_is_scalar(x_39)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_39;
}
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
if (lean_is_scalar(x_34)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_34;
}
lean_ctor_set(x_68, 0, x_67);
if (lean_is_scalar(x_46)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_46;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_64);
return x_69;
}
block_78:
{
if (x_71 == 0)
{
lean_dec(x_46);
lean_dec(x_39);
lean_dec(x_34);
x_57 = x_4;
x_58 = x_45;
goto block_62;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_inc(x_1);
lean_inc(x_41);
x_72 = l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg(x_41, x_1, x_4, x_45);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_1);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec_ref(x_72);
x_64 = x_75;
goto block_70;
}
else
{
if (x_16 == 0)
{
lean_object* x_76; 
lean_dec(x_46);
lean_dec(x_39);
lean_dec(x_34);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec_ref(x_72);
x_57 = x_4;
x_58 = x_76;
goto block_62;
}
else
{
lean_object* x_77; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_1);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_dec_ref(x_72);
x_64 = x_77;
goto block_70;
}
}
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_25);
if (x_82 == 0)
{
return x_25;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_25, 0);
x_84 = lean_ctor_get(x_25, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_25);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_7);
return x_87;
}
block_23:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_19 = lean_box(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
if (lean_is_scalar(x_15)) {
 x_21 = lean_alloc_ctor(1, 1, 0);
} else {
 x_21 = x_15;
}
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
x_10 = l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0___lam__0), 7, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = lean_box(0);
x_15 = l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0___closed__0;
x_16 = lean_array_size(x_9);
x_17 = 0;
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0_spec__1(x_13, x_15, x_14, x_9, x_16, x_17, x_15, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
lean_ctor_set(x_18, 0, x_11);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec_ref(x_20);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
lean_dec_ref(x_20);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_dec_ref(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("did not find equation for eliminating '", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substVar___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("variable '", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substVar___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is a let-declaration", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substVar___lam__0___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc_ref(x_3);
lean_inc(x_1);
x_8 = l_Lean_FVarId_getDecl___redArg(x_1, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = 0;
x_12 = l_Lean_LocalDecl_isLet(x_9, x_11);
lean_dec(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_13);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
x_14 = l_Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0(x_1, x_13, x_3, x_4, x_5, x_6, x_10);
lean_dec_ref(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Lean_Meta_substCore___lam__2___closed__1;
x_18 = l_Lean_Meta_substVar___lam__0___closed__1;
x_19 = l_Lean_mkFVar(x_1);
x_20 = l_Lean_MessageData_ofExpr(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Meta_substCore___lam__2___closed__18;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Meta_throwTacticEx___redArg(x_17, x_2, x_24, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; 
lean_dec(x_1);
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec_ref(x_15);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_dec_ref(x_14);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_box(0);
x_31 = 1;
x_32 = lean_unbox(x_29);
lean_dec(x_29);
x_33 = l_Lean_Meta_substCore(x_2, x_28, x_32, x_30, x_31, x_31, x_3, x_4, x_5, x_6, x_27);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
return x_33;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_33, 0);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_33);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_14);
if (x_45 == 0)
{
return x_14;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_14, 0);
x_47 = lean_ctor_get(x_14, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_14);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_49 = l_Lean_Meta_substCore___lam__2___closed__1;
x_50 = l_Lean_Meta_substVar___lam__0___closed__3;
x_51 = l_Lean_mkFVar(x_1);
x_52 = l_Lean_MessageData_ofExpr(x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Meta_substVar___lam__0___closed__5;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Lean_Meta_throwTacticEx___redArg(x_49, x_2, x_56, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_8);
if (x_62 == 0)
{
return x_8;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_8, 0);
x_64 = lean_ctor_get(x_8, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_8);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_substVar___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at___Lean_Meta_substCore_spec__10___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_subst_substEq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at___Lean_Meta_substCore_spec__1___closed__0;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_subst_substEq___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.subst.substEq", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_subst_substEq___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_substCore___lam__1___closed__7;
x_2 = lean_unsigned_to_nat(55u);
x_3 = lean_unsigned_to_nat(191u);
x_4 = l_Lean_Meta_subst_substEq___lam__0___closed__0;
x_5 = l_Lean_Meta_substCore___lam__1___closed__5;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_subst_substEq___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid equality proof, it is not of the form (x = t) or (t = x)", 64, 64);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_subst_substEq___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_subst_substEq___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_substEq___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc_ref(x_3);
lean_inc(x_1);
x_8 = l_Lean_FVarId_getDecl___redArg(x_1, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_50; lean_object* x_51; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_50 = l_Lean_LocalDecl_type(x_9);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_50);
x_51 = l_Lean_Meta_matchEq_x3f(x_50, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_50);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = l_Lean_Meta_subst_substEq___lam__0___closed__1;
x_55 = l_panic___at___Lean_Meta_subst_substEq_spec__0(x_54, x_3, x_4, x_5, x_6, x_53);
return x_55;
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_52, 0);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_57, 1);
x_60 = lean_ctor_get(x_57, 0);
lean_dec(x_60);
x_61 = lean_ctor_get(x_51, 1);
lean_inc(x_61);
lean_dec_ref(x_51);
x_62 = !lean_is_exclusive(x_59);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_64);
x_65 = lean_whnf(x_64, x_3, x_4, x_5, x_6, x_61);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec_ref(x_65);
x_68 = l_Lean_Expr_isFVar(x_66);
x_69 = 1;
if (x_68 == 0)
{
lean_object* x_84; 
lean_dec(x_66);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_63);
x_84 = lean_whnf(x_63, x_3, x_4, x_5, x_6, x_67);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_109; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
x_109 = l_Lean_Expr_isFVar(x_85);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_9);
lean_dec(x_1);
x_110 = l_Lean_Meta_substCore___lam__2___closed__1;
x_111 = l_Lean_Meta_subst_substEq___lam__0___closed__3;
x_112 = l_Lean_indentExpr(x_50);
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_112);
lean_ctor_set(x_59, 0, x_111);
x_113 = l_Lean_Meta_substCore___lam__1___closed__4;
lean_ctor_set_tag(x_57, 7);
lean_ctor_set(x_57, 1, x_113);
lean_ctor_set(x_57, 0, x_59);
x_114 = l_Lean_Meta_throwTacticEx___redArg(x_110, x_2, x_52, x_3, x_4, x_5, x_6, x_86);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_114;
}
else
{
uint8_t x_115; 
lean_free_object(x_59);
lean_free_object(x_57);
lean_free_object(x_52);
lean_dec_ref(x_50);
x_115 = lean_expr_eqv(x_63, x_85);
lean_dec(x_63);
if (x_115 == 0)
{
x_87 = x_109;
goto block_108;
}
else
{
x_87 = x_68;
goto block_108;
}
}
block_108:
{
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_85);
lean_dec(x_64);
lean_dec(x_9);
x_88 = lean_box(0);
x_89 = l_Lean_Meta_substCore(x_2, x_1, x_87, x_88, x_69, x_69, x_3, x_4, x_5, x_6, x_86);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
lean_ctor_set(x_89, 0, x_92);
return x_89;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_89, 0);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_89);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_89);
if (x_97 == 0)
{
return x_89;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_89, 0);
x_99 = lean_ctor_get(x_89, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_89);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_101 = l_Lean_Meta_mkEq(x_85, x_64, x_3, x_4, x_5, x_6, x_86);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec_ref(x_101);
x_11 = x_102;
x_12 = x_68;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_103;
goto block_49;
}
else
{
uint8_t x_104; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_101);
if (x_104 == 0)
{
return x_101;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_101, 0);
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_101);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
}
else
{
uint8_t x_116; 
lean_free_object(x_59);
lean_dec(x_64);
lean_dec(x_63);
lean_free_object(x_57);
lean_free_object(x_52);
lean_dec_ref(x_50);
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_84);
if (x_116 == 0)
{
return x_84;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_84, 0);
x_118 = lean_ctor_get(x_84, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_84);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_free_object(x_59);
lean_free_object(x_57);
lean_free_object(x_52);
lean_dec_ref(x_50);
x_120 = lean_expr_eqv(x_64, x_66);
lean_dec(x_64);
if (x_120 == 0)
{
if (x_68 == 0)
{
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_9);
goto block_83;
}
else
{
lean_object* x_121; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_121 = l_Lean_Meta_mkEq(x_63, x_66, x_3, x_4, x_5, x_6, x_67);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec_ref(x_121);
x_11 = x_122;
x_12 = x_69;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_123;
goto block_49;
}
else
{
uint8_t x_124; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_121);
if (x_124 == 0)
{
return x_121;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_121, 0);
x_126 = lean_ctor_get(x_121, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_121);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
else
{
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_9);
goto block_83;
}
}
block_83:
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_box(0);
x_71 = l_Lean_Meta_substCore(x_2, x_1, x_69, x_70, x_69, x_69, x_3, x_4, x_5, x_6, x_67);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
lean_ctor_set(x_71, 0, x_74);
return x_71;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_71, 0);
x_76 = lean_ctor_get(x_71, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_71);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_71);
if (x_79 == 0)
{
return x_71;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_71, 0);
x_81 = lean_ctor_get(x_71, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_71);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
uint8_t x_128; 
lean_free_object(x_59);
lean_dec(x_64);
lean_dec(x_63);
lean_free_object(x_57);
lean_free_object(x_52);
lean_dec_ref(x_50);
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_65);
if (x_128 == 0)
{
return x_65;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_65, 0);
x_130 = lean_ctor_get(x_65, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_65);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_59, 0);
x_133 = lean_ctor_get(x_59, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_59);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_133);
x_134 = lean_whnf(x_133, x_3, x_4, x_5, x_6, x_61);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec_ref(x_134);
x_137 = l_Lean_Expr_isFVar(x_135);
x_138 = 1;
if (x_137 == 0)
{
lean_object* x_151; 
lean_dec(x_135);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_132);
x_151 = lean_whnf(x_132, x_3, x_4, x_5, x_6, x_136);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; uint8_t x_174; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec_ref(x_151);
x_174 = l_Lean_Expr_isFVar(x_152);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_152);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_9);
lean_dec(x_1);
x_175 = l_Lean_Meta_substCore___lam__2___closed__1;
x_176 = l_Lean_Meta_subst_substEq___lam__0___closed__3;
x_177 = l_Lean_indentExpr(x_50);
x_178 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_179 = l_Lean_Meta_substCore___lam__1___closed__4;
lean_ctor_set_tag(x_57, 7);
lean_ctor_set(x_57, 1, x_179);
lean_ctor_set(x_57, 0, x_178);
x_180 = l_Lean_Meta_throwTacticEx___redArg(x_175, x_2, x_52, x_3, x_4, x_5, x_6, x_153);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_180;
}
else
{
uint8_t x_181; 
lean_free_object(x_57);
lean_free_object(x_52);
lean_dec_ref(x_50);
x_181 = lean_expr_eqv(x_132, x_152);
lean_dec(x_132);
if (x_181 == 0)
{
x_154 = x_174;
goto block_173;
}
else
{
x_154 = x_137;
goto block_173;
}
}
block_173:
{
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_152);
lean_dec(x_133);
lean_dec(x_9);
x_155 = lean_box(0);
x_156 = l_Lean_Meta_substCore(x_2, x_1, x_154, x_155, x_138, x_138, x_3, x_4, x_5, x_6, x_153);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
lean_dec(x_157);
if (lean_is_scalar(x_159)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_159;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_158);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_156, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_156, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_164 = x_156;
} else {
 lean_dec_ref(x_156);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
else
{
lean_object* x_166; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_166 = l_Lean_Meta_mkEq(x_152, x_133, x_3, x_4, x_5, x_6, x_153);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec_ref(x_166);
x_11 = x_167;
x_12 = x_137;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_168;
goto block_49;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = lean_ctor_get(x_166, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_166, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_171 = x_166;
} else {
 lean_dec_ref(x_166);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_133);
lean_dec(x_132);
lean_free_object(x_57);
lean_free_object(x_52);
lean_dec_ref(x_50);
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_182 = lean_ctor_get(x_151, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_151, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_184 = x_151;
} else {
 lean_dec_ref(x_151);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
uint8_t x_186; 
lean_free_object(x_57);
lean_free_object(x_52);
lean_dec_ref(x_50);
x_186 = lean_expr_eqv(x_133, x_135);
lean_dec(x_133);
if (x_186 == 0)
{
if (x_137 == 0)
{
lean_dec(x_135);
lean_dec(x_132);
lean_dec(x_9);
goto block_150;
}
else
{
lean_object* x_187; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_187 = l_Lean_Meta_mkEq(x_132, x_135, x_3, x_4, x_5, x_6, x_136);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec_ref(x_187);
x_11 = x_188;
x_12 = x_138;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_189;
goto block_49;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_190 = lean_ctor_get(x_187, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_187, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_192 = x_187;
} else {
 lean_dec_ref(x_187);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
}
else
{
lean_dec(x_135);
lean_dec(x_132);
lean_dec(x_9);
goto block_150;
}
}
block_150:
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_box(0);
x_140 = l_Lean_Meta_substCore(x_2, x_1, x_138, x_139, x_138, x_138, x_3, x_4, x_5, x_6, x_136);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_143 = x_140;
} else {
 lean_dec_ref(x_140);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec(x_141);
if (lean_is_scalar(x_143)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_143;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_142);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_140, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_140, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_148 = x_140;
} else {
 lean_dec_ref(x_140);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_133);
lean_dec(x_132);
lean_free_object(x_57);
lean_free_object(x_52);
lean_dec_ref(x_50);
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_194 = lean_ctor_get(x_134, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_134, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_196 = x_134;
} else {
 lean_dec_ref(x_134);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_198 = lean_ctor_get(x_57, 1);
lean_inc(x_198);
lean_dec(x_57);
x_199 = lean_ctor_get(x_51, 1);
lean_inc(x_199);
lean_dec_ref(x_51);
x_200 = lean_ctor_get(x_198, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_202 = x_198;
} else {
 lean_dec_ref(x_198);
 x_202 = lean_box(0);
}
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_201);
x_203 = lean_whnf(x_201, x_3, x_4, x_5, x_6, x_199);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; uint8_t x_206; uint8_t x_207; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec_ref(x_203);
x_206 = l_Lean_Expr_isFVar(x_204);
x_207 = 1;
if (x_206 == 0)
{
lean_object* x_220; 
lean_dec(x_204);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_200);
x_220 = lean_whnf(x_200, x_3, x_4, x_5, x_6, x_205);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; uint8_t x_243; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec_ref(x_220);
x_243 = l_Lean_Expr_isFVar(x_221);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_221);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_9);
lean_dec(x_1);
x_244 = l_Lean_Meta_substCore___lam__2___closed__1;
x_245 = l_Lean_Meta_subst_substEq___lam__0___closed__3;
x_246 = l_Lean_indentExpr(x_50);
if (lean_is_scalar(x_202)) {
 x_247 = lean_alloc_ctor(7, 2, 0);
} else {
 x_247 = x_202;
 lean_ctor_set_tag(x_247, 7);
}
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_248 = l_Lean_Meta_substCore___lam__1___closed__4;
x_249 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
lean_ctor_set(x_52, 0, x_249);
x_250 = l_Lean_Meta_throwTacticEx___redArg(x_244, x_2, x_52, x_3, x_4, x_5, x_6, x_222);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_250;
}
else
{
uint8_t x_251; 
lean_dec(x_202);
lean_free_object(x_52);
lean_dec_ref(x_50);
x_251 = lean_expr_eqv(x_200, x_221);
lean_dec(x_200);
if (x_251 == 0)
{
x_223 = x_243;
goto block_242;
}
else
{
x_223 = x_206;
goto block_242;
}
}
block_242:
{
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; 
lean_dec(x_221);
lean_dec(x_201);
lean_dec(x_9);
x_224 = lean_box(0);
x_225 = l_Lean_Meta_substCore(x_2, x_1, x_223, x_224, x_207, x_207, x_3, x_4, x_5, x_6, x_222);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_228 = x_225;
} else {
 lean_dec_ref(x_225);
 x_228 = lean_box(0);
}
x_229 = lean_ctor_get(x_226, 1);
lean_inc(x_229);
lean_dec(x_226);
if (lean_is_scalar(x_228)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_228;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_227);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_231 = lean_ctor_get(x_225, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_225, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_233 = x_225;
} else {
 lean_dec_ref(x_225);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
else
{
lean_object* x_235; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_235 = l_Lean_Meta_mkEq(x_221, x_201, x_3, x_4, x_5, x_6, x_222);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec_ref(x_235);
x_11 = x_236;
x_12 = x_206;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_237;
goto block_49;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_238 = lean_ctor_get(x_235, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_235, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_240 = x_235;
} else {
 lean_dec_ref(x_235);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_free_object(x_52);
lean_dec_ref(x_50);
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_252 = lean_ctor_get(x_220, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_220, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_254 = x_220;
} else {
 lean_dec_ref(x_220);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
}
else
{
uint8_t x_256; 
lean_dec(x_202);
lean_free_object(x_52);
lean_dec_ref(x_50);
x_256 = lean_expr_eqv(x_201, x_204);
lean_dec(x_201);
if (x_256 == 0)
{
if (x_206 == 0)
{
lean_dec(x_204);
lean_dec(x_200);
lean_dec(x_9);
goto block_219;
}
else
{
lean_object* x_257; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_257 = l_Lean_Meta_mkEq(x_200, x_204, x_3, x_4, x_5, x_6, x_205);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec_ref(x_257);
x_11 = x_258;
x_12 = x_207;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_259;
goto block_49;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_260 = lean_ctor_get(x_257, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_257, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_262 = x_257;
} else {
 lean_dec_ref(x_257);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
}
else
{
lean_dec(x_204);
lean_dec(x_200);
lean_dec(x_9);
goto block_219;
}
}
block_219:
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_box(0);
x_209 = l_Lean_Meta_substCore(x_2, x_1, x_207, x_208, x_207, x_207, x_3, x_4, x_5, x_6, x_205);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_212 = x_209;
} else {
 lean_dec_ref(x_209);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
lean_dec(x_210);
if (lean_is_scalar(x_212)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_212;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_211);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_215 = lean_ctor_get(x_209, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_209, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_217 = x_209;
} else {
 lean_dec_ref(x_209);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_216);
return x_218;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_free_object(x_52);
lean_dec_ref(x_50);
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_264 = lean_ctor_get(x_203, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_203, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_266 = x_203;
} else {
 lean_dec_ref(x_203);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_268 = lean_ctor_get(x_52, 0);
lean_inc(x_268);
lean_dec(x_52);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_270 = x_268;
} else {
 lean_dec_ref(x_268);
 x_270 = lean_box(0);
}
x_271 = lean_ctor_get(x_51, 1);
lean_inc(x_271);
lean_dec_ref(x_51);
x_272 = lean_ctor_get(x_269, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_269, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_274 = x_269;
} else {
 lean_dec_ref(x_269);
 x_274 = lean_box(0);
}
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_273);
x_275 = lean_whnf(x_273, x_3, x_4, x_5, x_6, x_271);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; uint8_t x_279; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec_ref(x_275);
x_278 = l_Lean_Expr_isFVar(x_276);
x_279 = 1;
if (x_278 == 0)
{
lean_object* x_292; 
lean_dec(x_276);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_272);
x_292 = lean_whnf(x_272, x_3, x_4, x_5, x_6, x_277);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; uint8_t x_315; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec_ref(x_292);
x_315 = l_Lean_Expr_isFVar(x_293);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_293);
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_9);
lean_dec(x_1);
x_316 = l_Lean_Meta_substCore___lam__2___closed__1;
x_317 = l_Lean_Meta_subst_substEq___lam__0___closed__3;
x_318 = l_Lean_indentExpr(x_50);
if (lean_is_scalar(x_274)) {
 x_319 = lean_alloc_ctor(7, 2, 0);
} else {
 x_319 = x_274;
 lean_ctor_set_tag(x_319, 7);
}
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
x_320 = l_Lean_Meta_substCore___lam__1___closed__4;
if (lean_is_scalar(x_270)) {
 x_321 = lean_alloc_ctor(7, 2, 0);
} else {
 x_321 = x_270;
 lean_ctor_set_tag(x_321, 7);
}
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
x_322 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_322, 0, x_321);
x_323 = l_Lean_Meta_throwTacticEx___redArg(x_316, x_2, x_322, x_3, x_4, x_5, x_6, x_294);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_323;
}
else
{
uint8_t x_324; 
lean_dec(x_274);
lean_dec(x_270);
lean_dec_ref(x_50);
x_324 = lean_expr_eqv(x_272, x_293);
lean_dec(x_272);
if (x_324 == 0)
{
x_295 = x_315;
goto block_314;
}
else
{
x_295 = x_278;
goto block_314;
}
}
block_314:
{
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; 
lean_dec(x_293);
lean_dec(x_273);
lean_dec(x_9);
x_296 = lean_box(0);
x_297 = l_Lean_Meta_substCore(x_2, x_1, x_295, x_296, x_279, x_279, x_3, x_4, x_5, x_6, x_294);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_300 = x_297;
} else {
 lean_dec_ref(x_297);
 x_300 = lean_box(0);
}
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_dec(x_298);
if (lean_is_scalar(x_300)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_300;
}
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_299);
return x_302;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_303 = lean_ctor_get(x_297, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_297, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_305 = x_297;
} else {
 lean_dec_ref(x_297);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_303);
lean_ctor_set(x_306, 1, x_304);
return x_306;
}
}
else
{
lean_object* x_307; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_307 = l_Lean_Meta_mkEq(x_293, x_273, x_3, x_4, x_5, x_6, x_294);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec_ref(x_307);
x_11 = x_308;
x_12 = x_278;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_309;
goto block_49;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_310 = lean_ctor_get(x_307, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_307, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_312 = x_307;
} else {
 lean_dec_ref(x_307);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_310);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
}
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_270);
lean_dec_ref(x_50);
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_325 = lean_ctor_get(x_292, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_292, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_327 = x_292;
} else {
 lean_dec_ref(x_292);
 x_327 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_328 = lean_alloc_ctor(1, 2, 0);
} else {
 x_328 = x_327;
}
lean_ctor_set(x_328, 0, x_325);
lean_ctor_set(x_328, 1, x_326);
return x_328;
}
}
else
{
uint8_t x_329; 
lean_dec(x_274);
lean_dec(x_270);
lean_dec_ref(x_50);
x_329 = lean_expr_eqv(x_273, x_276);
lean_dec(x_273);
if (x_329 == 0)
{
if (x_278 == 0)
{
lean_dec(x_276);
lean_dec(x_272);
lean_dec(x_9);
goto block_291;
}
else
{
lean_object* x_330; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_330 = l_Lean_Meta_mkEq(x_272, x_276, x_3, x_4, x_5, x_6, x_277);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec_ref(x_330);
x_11 = x_331;
x_12 = x_279;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_332;
goto block_49;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_333 = lean_ctor_get(x_330, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_330, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_335 = x_330;
} else {
 lean_dec_ref(x_330);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(1, 2, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_333);
lean_ctor_set(x_336, 1, x_334);
return x_336;
}
}
}
else
{
lean_dec(x_276);
lean_dec(x_272);
lean_dec(x_9);
goto block_291;
}
}
block_291:
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_box(0);
x_281 = l_Lean_Meta_substCore(x_2, x_1, x_279, x_280, x_279, x_279, x_3, x_4, x_5, x_6, x_277);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_284 = x_281;
} else {
 lean_dec_ref(x_281);
 x_284 = lean_box(0);
}
x_285 = lean_ctor_get(x_282, 1);
lean_inc(x_285);
lean_dec(x_282);
if (lean_is_scalar(x_284)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_284;
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_283);
return x_286;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_287 = lean_ctor_get(x_281, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_281, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_289 = x_281;
} else {
 lean_dec_ref(x_281);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_288);
return x_290;
}
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_270);
lean_dec_ref(x_50);
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_337 = lean_ctor_get(x_275, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_275, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_339 = x_275;
} else {
 lean_dec_ref(x_275);
 x_339 = lean_box(0);
}
if (lean_is_scalar(x_339)) {
 x_340 = lean_alloc_ctor(1, 2, 0);
} else {
 x_340 = x_339;
}
lean_ctor_set(x_340, 0, x_337);
lean_ctor_set(x_340, 1, x_338);
return x_340;
}
}
}
}
else
{
uint8_t x_341; 
lean_dec_ref(x_50);
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_341 = !lean_is_exclusive(x_51);
if (x_341 == 0)
{
return x_51;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_51, 0);
x_343 = lean_ctor_get(x_51, 1);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_51);
x_344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
return x_344;
}
}
block_49:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l_Lean_LocalDecl_userName(x_9);
lean_dec(x_9);
lean_inc(x_1);
x_19 = l_Lean_mkFVar(x_1);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_20 = l_Lean_MVarId_assert(x_2, x_18, x_11, x_19, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = 1;
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_24 = l_Lean_Meta_intro1Core(x_21, x_23, x_13, x_14, x_15, x_16, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_29 = l_Lean_MVarId_clear(x_28, x_1, x_13, x_14, x_15, x_16, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_box(0);
x_33 = l_Lean_Meta_substCore(x_30, x_27, x_12, x_32, x_23, x_23, x_13, x_14, x_15, x_16, x_31);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
return x_33;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_33, 0);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_33);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
return x_29;
}
}
else
{
uint8_t x_45; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_24);
if (x_45 == 0)
{
return x_24;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_24, 0);
x_47 = lean_ctor_get(x_24, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_24);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_1);
return x_20;
}
}
}
else
{
uint8_t x_345; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_345 = !lean_is_exclusive(x_8);
if (x_345 == 0)
{
return x_8;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_8, 0);
x_347 = lean_ctor_get(x_8, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_8);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
return x_348;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_substEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_subst_substEq___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at___Lean_Meta_substCore_spec__10___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc_ref(x_3);
lean_inc(x_1);
x_8 = l_Lean_FVarId_getType___redArg(x_1, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_9);
x_11 = l_Lean_Meta_matchEq_x3f(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_14 = l_Lean_Meta_matchHEq_x3f(x_9, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Lean_Meta_substVar(x_2, x_1, x_3, x_4, x_5, x_6, x_16);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec_ref(x_14);
x_19 = 1;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_20 = l_Lean_Meta_heqToEq(x_2, x_1, x_19, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lean_beqMVarId____x40_Lean_Expr___hyg_1814_(x_2, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_26 = l_Lean_Meta_subst(x_24, x_23, x_3, x_4, x_5, x_6, x_22);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_23);
x_27 = l_Lean_Meta_substVar(x_2, x_1, x_3, x_4, x_5, x_6, x_22);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec_ref(x_12);
lean_dec(x_9);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_dec_ref(x_11);
x_37 = l_Lean_Meta_subst_substEq(x_2, x_1, x_3, x_4, x_5, x_6, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_11);
if (x_38 == 0)
{
return x_11;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_11, 0);
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_11);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
return x_8;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_8, 0);
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_8);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_subst___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at___Lean_Meta_substCore_spec__10___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___Lean_Meta_substVar_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___redArg(x_3, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_inc(x_5);
lean_inc(x_3);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_31; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_20 = x_10;
} else {
 lean_dec_ref(x_10);
 x_20 = lean_box(0);
}
x_31 = l_Lean_Exception_isInterrupt(x_18);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = l_Lean_Exception_isRuntime(x_18);
x_21 = x_32;
goto block_30;
}
else
{
x_21 = x_31;
goto block_30;
}
block_30:
{
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_20);
lean_dec(x_18);
x_22 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5, x_19);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_8);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
if (lean_is_scalar(x_20)) {
 x_29 = lean_alloc_ctor(1, 2, 0);
} else {
 x_29 = x_20;
}
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_19);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___Lean_Meta_substVar_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_observing_x3f___at___Lean_Meta_substVar_x3f_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_substVar), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_observing_x3f___at___Lean_Meta_substVar_x3f_spec__0___redArg(x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_subst), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = l_Lean_observing_x3f___at___Lean_Meta_substVar_x3f_spec__0___redArg(x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_box(x_3);
x_13 = lean_box(x_5);
x_14 = lean_box(x_6);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___boxed), 11, 6);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_12);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_13);
lean_closure_set(x_15, 5, x_14);
x_16 = l_Lean_observing_x3f___at___Lean_Meta_substVar_x3f_spec__0___redArg(x_15, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_3);
x_13 = lean_unbox(x_5);
x_14 = lean_unbox(x_6);
x_15 = l_Lean_Meta_substCore_x3f(x_1, x_2, x_12, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Meta_substVar_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec_ref(x_9);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec_ref(x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Meta_subst_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec_ref(x_9);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec_ref(x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_8, x_7);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_9, 1);
x_19 = lean_ctor_get(x_9, 0);
lean_dec(x_19);
x_20 = lean_array_uget(x_6, x_8);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_18);
lean_inc_ref(x_2);
lean_inc(x_1);
x_21 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_20, x_18, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_9, 0, x_25);
lean_ctor_set(x_21, 0, x_9);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_9, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
lean_dec(x_18);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec_ref(x_21);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec_ref(x_22);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_30);
lean_ctor_set(x_9, 0, x_5);
x_31 = 1;
x_32 = lean_usize_add(x_8, x_31);
x_8 = x_32;
x_14 = x_29;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_9);
lean_dec(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
lean_dec(x_9);
x_39 = lean_array_uget(x_6, x_8);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_38);
lean_inc_ref(x_2);
lean_inc(x_1);
x_40 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_39, x_38, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_38);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; 
lean_dec(x_38);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_dec_ref(x_40);
x_48 = lean_ctor_get(x_41, 0);
lean_inc(x_48);
lean_dec_ref(x_41);
lean_inc(x_5);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_5);
lean_ctor_set(x_49, 1, x_48);
x_50 = 1;
x_51 = lean_usize_add(x_8, x_50);
x_8 = x_51;
x_9 = x_49;
x_14 = x_47;
goto _start;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_38);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_40, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_40, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_55 = x_40;
} else {
 lean_dec_ref(x_40);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
x_17 = lean_array_uget(x_3, x_5);
lean_inc_ref(x_1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_15);
x_18 = lean_apply_7(x_1, x_17, x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_6, 0, x_22);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_6, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
lean_dec(x_15);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec_ref(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec_ref(x_19);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_27);
lean_ctor_set(x_6, 0, x_2);
x_28 = 1;
x_29 = lean_usize_add(x_5, x_28);
x_5 = x_29;
x_11 = x_26;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
lean_dec(x_6);
x_36 = lean_array_uget(x_3, x_5);
lean_inc_ref(x_1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_35);
x_37 = lean_apply_7(x_1, x_36, x_35, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; 
lean_dec(x_35);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec_ref(x_37);
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec_ref(x_38);
lean_inc(x_2);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_45);
x_47 = 1;
x_48 = lean_usize_add(x_5, x_47);
x_5 = x_48;
x_6 = x_46;
x_11 = x_44;
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_35);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_50 = lean_ctor_get(x_37, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_52 = x_37;
} else {
 lean_dec_ref(x_37);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec_ref(x_5);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = l_Lean_Meta_subst_x3f(x_1, x_15, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_free_object(x_4);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec_ref(x_2);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_16, 0);
lean_dec(x_25);
lean_inc_ref(x_17);
lean_ctor_set(x_4, 0, x_17);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_dec(x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 0, x_28);
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_17);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_3);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_dec(x_16);
lean_inc_ref(x_17);
lean_ctor_set(x_4, 0, x_17);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_32 = x_17;
} else {
 lean_dec_ref(x_17);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_3);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_32;
 lean_ctor_set_tag(x_34, 0);
}
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_free_object(x_4);
lean_dec_ref(x_2);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_16);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_4, 0);
lean_inc(x_40);
lean_dec(x_4);
x_41 = l_Lean_LocalDecl_fvarId(x_40);
lean_dec(x_40);
x_42 = l_Lean_Meta_subst_x3f(x_1, x_41, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_2);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_2);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_49 = x_42;
} else {
 lean_dec_ref(x_42);
 x_49 = lean_box(0);
}
lean_inc_ref(x_43);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_43);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_51 = x_43;
} else {
 lean_dec_ref(x_43);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_3);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_51;
 lean_ctor_set_tag(x_53, 0);
}
lean_ctor_set(x_53, 0, x_52);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_48);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_2);
x_55 = lean_ctor_get(x_42, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_57 = x_42;
} else {
 lean_dec_ref(x_42);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
x_16 = lean_array_size(x_13);
x_17 = 0;
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_14, x_13, x_16, x_17, x_15, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_23);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_19);
lean_free_object(x_5);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
lean_dec_ref(x_20);
lean_ctor_set(x_18, 0, x_29);
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec(x_18);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec_ref(x_20);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_free_object(x_5);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_5, 0);
lean_inc(x_37);
lean_dec(x_5);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_6);
x_40 = lean_array_size(x_37);
x_41 = 0;
x_42 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_38, x_37, x_40, x_41, x_39, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_37);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_46 = x_42;
} else {
 lean_dec_ref(x_42);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_43);
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_51 = x_42;
} else {
 lean_dec_ref(x_42);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_44, 0);
lean_inc(x_52);
lean_dec_ref(x_44);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_42, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_42, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_56 = x_42;
} else {
 lean_dec_ref(x_42);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_5);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; size_t x_63; size_t x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_5, 0);
x_60 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0___lam__0), 10, 3);
lean_closure_set(x_60, 0, x_1);
lean_closure_set(x_60, 1, x_2);
lean_closure_set(x_60, 2, x_3);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_6);
x_63 = lean_array_size(x_59);
x_64 = 0;
x_65 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(x_60, x_61, x_59, x_63, x_64, x_62, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_59);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_65, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
lean_ctor_set(x_5, 0, x_70);
lean_ctor_set(x_65, 0, x_5);
return x_65;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
lean_dec(x_65);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_dec(x_66);
lean_ctor_set(x_5, 0, x_72);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_5);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_66);
lean_free_object(x_5);
x_74 = !lean_is_exclusive(x_65);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_65, 0);
lean_dec(x_75);
x_76 = lean_ctor_get(x_67, 0);
lean_inc(x_76);
lean_dec_ref(x_67);
lean_ctor_set(x_65, 0, x_76);
return x_65;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_65, 1);
lean_inc(x_77);
lean_dec(x_65);
x_78 = lean_ctor_get(x_67, 0);
lean_inc(x_78);
lean_dec_ref(x_67);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_free_object(x_5);
x_80 = !lean_is_exclusive(x_65);
if (x_80 == 0)
{
return x_65;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_65, 0);
x_82 = lean_ctor_get(x_65, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_65);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; size_t x_88; size_t x_89; lean_object* x_90; 
x_84 = lean_ctor_get(x_5, 0);
lean_inc(x_84);
lean_dec(x_5);
x_85 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0___lam__0), 10, 3);
lean_closure_set(x_85, 0, x_1);
lean_closure_set(x_85, 1, x_2);
lean_closure_set(x_85, 2, x_3);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_6);
x_88 = lean_array_size(x_84);
x_89 = 0;
x_90 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(x_85, x_86, x_84, x_88, x_89, x_87, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_84);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_94 = x_90;
} else {
 lean_dec_ref(x_90);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
lean_dec(x_91);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
if (lean_is_scalar(x_94)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_94;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_93);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_91);
x_98 = lean_ctor_get(x_90, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_99 = x_90;
} else {
 lean_dec_ref(x_90);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_92, 0);
lean_inc(x_100);
lean_dec_ref(x_92);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_90, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_90, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_104 = x_90;
} else {
 lean_dec_ref(x_90);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
x_17 = lean_array_uget(x_3, x_5);
lean_inc_ref(x_1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_15);
x_18 = lean_apply_7(x_1, x_17, x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_6, 0, x_19);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_27 = x_19;
} else {
 lean_dec_ref(x_19);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_27;
 lean_ctor_set_tag(x_28, 1);
}
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_6, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_15);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec_ref(x_18);
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
lean_dec_ref(x_19);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_31);
lean_ctor_set(x_6, 0, x_2);
x_32 = 1;
x_33 = lean_usize_add(x_5, x_32);
x_5 = x_33;
x_11 = x_30;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
return x_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_18, 0);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_18);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_6, 1);
lean_inc(x_39);
lean_dec(x_6);
x_40 = lean_array_uget(x_3, x_5);
lean_inc_ref(x_1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_39);
x_41 = lean_apply_7(x_1, x_40, x_39, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_46 = x_42;
} else {
 lean_dec_ref(x_42);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_46;
 lean_ctor_set_tag(x_47, 1);
}
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_39);
if (lean_is_scalar(x_44)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_44;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; 
lean_dec(x_39);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec_ref(x_41);
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
lean_dec_ref(x_42);
lean_inc(x_2);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_51);
x_53 = 1;
x_54 = lean_usize_add(x_5, x_53);
x_5 = x_54;
x_6 = x_52;
x_11 = x_50;
goto _start;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_39);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_56 = lean_ctor_get(x_41, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_58 = x_41;
} else {
 lean_dec_ref(x_41);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec_ref(x_5);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = l_Lean_LocalDecl_fvarId(x_14);
lean_dec(x_14);
x_16 = l_Lean_Meta_subst_x3f(x_1, x_15, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_free_object(x_4);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec_ref(x_2);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_16, 0);
lean_dec(x_25);
lean_inc_ref(x_17);
lean_ctor_set(x_4, 0, x_17);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_dec(x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 0, x_28);
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_17);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_3);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_dec(x_16);
lean_inc_ref(x_17);
lean_ctor_set(x_4, 0, x_17);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_32 = x_17;
} else {
 lean_dec_ref(x_17);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_3);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_32;
 lean_ctor_set_tag(x_34, 0);
}
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_free_object(x_4);
lean_dec_ref(x_2);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
return x_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_16, 0);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_16);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_4, 0);
lean_inc(x_40);
lean_dec(x_4);
x_41 = l_Lean_LocalDecl_fvarId(x_40);
lean_dec(x_40);
x_42 = l_Lean_Meta_subst_x3f(x_1, x_41, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_2);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_2);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_49 = x_42;
} else {
 lean_dec_ref(x_42);
 x_49 = lean_box(0);
}
lean_inc_ref(x_43);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_43);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_51 = x_43;
} else {
 lean_dec_ref(x_43);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_3);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_51;
 lean_ctor_set_tag(x_53, 0);
}
lean_ctor_set(x_53, 0, x_52);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_48);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_2);
x_55 = lean_ctor_get(x_42, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_57 = x_42;
} else {
 lean_dec_ref(x_42);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
lean_inc(x_1);
x_13 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0(x_1, x_2, x_3, x_5, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec_ref(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec_ref(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec_ref(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec_ref(x_14);
x_23 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0___lam__0), 10, 3);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_3);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_array_size(x_12);
x_27 = 0;
x_28 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__3(x_23, x_24, x_12, x_26, x_27, x_25, x_6, x_7, x_8, x_9, x_21);
lean_dec_ref(x_12);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_28, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_29);
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_28, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
lean_dec_ref(x_30);
lean_ctor_set(x_28, 0, x_39);
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_dec(x_28);
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_41);
lean_dec_ref(x_30);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_28);
if (x_43 == 0)
{
return x_28;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_28, 0);
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_28);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_13);
if (x_47 == 0)
{
return x_13;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_13, 0);
x_49 = lean_ctor_get(x_13, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_13);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
static lean_object* _init_l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lean_box(0);
x_10 = l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0;
x_11 = l_Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0(x_1, x_10, x_9, x_8, x_10, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_11, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec_ref(x_13);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec_ref(x_13);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_substSomeVar_x3f___lam__0), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_MVarId_withContext___at___Lean_Meta_substCore_spec__10___redArg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_16, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Meta_substSomeVar_x3f_spec__0_spec__3(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_substSomeVar_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec_ref(x_7);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec_ref(x_8);
x_1 = x_14;
x_6 = x_13;
goto _start;
}
}
else
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Subst___hyg_3853_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Subst___hyg_3853_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Subst___hyg_3853_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lam__2___closed__21;
x_2 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Subst___hyg_3853_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Subst___hyg_3853_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
x_2 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Subst___hyg_3853_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Subst___hyg_3853_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
x_2 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Subst___hyg_3853_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
x_2 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Subst___hyg_3853_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lam__2___closed__21;
x_2 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Subst___hyg_3853_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lam__2___closed__22;
x_2 = l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Subst___hyg_3853_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Subst", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Subst___hyg_3853_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
x_2 = l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Subst___hyg_3853_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Subst___hyg_3853_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
x_2 = l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Subst___hyg_3853_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3853u);
x_2 = l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3853_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_substCore___lam__2___closed__23;
x_3 = 0;
x_4 = l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Subst___hyg_3853_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_FVarSubst(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at___Lean_Meta_substCore_spec__1___closed__0 = _init_l_panic___at___Lean_Meta_substCore_spec__1___closed__0();
lean_mark_persistent(l_panic___at___Lean_Meta_substCore_spec__1___closed__0);
l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__0 = _init_l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__0();
l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__1 = _init_l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__1);
l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__2 = _init_l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Meta_substCore_spec__4___closed__2);
l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__0 = _init_l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__0();
lean_mark_persistent(l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__0);
l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__1 = _init_l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__1();
lean_mark_persistent(l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__1);
l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__2 = _init_l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__2();
lean_mark_persistent(l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__2);
l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__3 = _init_l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__3();
lean_mark_persistent(l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__3);
l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__4 = _init_l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__4();
lean_mark_persistent(l_Lean_exprDependsOn___at___Lean_Meta_substCore_spec__6___redArg___closed__4);
l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg___closed__0 = _init_l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg___closed__0();
lean_mark_persistent(l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg___closed__0);
l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg___closed__1 = _init_l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg___closed__1();
lean_mark_persistent(l_Lean_MVarId_assign___at___Lean_Meta_substCore_spec__7___redArg___closed__1);
l_Lean_Meta_substCore___lam__1___closed__0 = _init_l_Lean_Meta_substCore___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_substCore___lam__1___closed__0);
l_Lean_Meta_substCore___lam__1___closed__1 = _init_l_Lean_Meta_substCore___lam__1___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lam__1___closed__1);
l_Lean_Meta_substCore___lam__1___closed__2 = _init_l_Lean_Meta_substCore___lam__1___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lam__1___closed__2);
l_Lean_Meta_substCore___lam__1___closed__3 = _init_l_Lean_Meta_substCore___lam__1___closed__3();
lean_mark_persistent(l_Lean_Meta_substCore___lam__1___closed__3);
l_Lean_Meta_substCore___lam__1___closed__4 = _init_l_Lean_Meta_substCore___lam__1___closed__4();
lean_mark_persistent(l_Lean_Meta_substCore___lam__1___closed__4);
l_Lean_Meta_substCore___lam__1___closed__5 = _init_l_Lean_Meta_substCore___lam__1___closed__5();
lean_mark_persistent(l_Lean_Meta_substCore___lam__1___closed__5);
l_Lean_Meta_substCore___lam__1___closed__6 = _init_l_Lean_Meta_substCore___lam__1___closed__6();
lean_mark_persistent(l_Lean_Meta_substCore___lam__1___closed__6);
l_Lean_Meta_substCore___lam__1___closed__7 = _init_l_Lean_Meta_substCore___lam__1___closed__7();
lean_mark_persistent(l_Lean_Meta_substCore___lam__1___closed__7);
l_Lean_Meta_substCore___lam__1___closed__8 = _init_l_Lean_Meta_substCore___lam__1___closed__8();
lean_mark_persistent(l_Lean_Meta_substCore___lam__1___closed__8);
l_Lean_Meta_substCore___lam__1___closed__9 = _init_l_Lean_Meta_substCore___lam__1___closed__9();
lean_mark_persistent(l_Lean_Meta_substCore___lam__1___closed__9);
l_Lean_Meta_substCore___lam__1___closed__10 = _init_l_Lean_Meta_substCore___lam__1___closed__10();
lean_mark_persistent(l_Lean_Meta_substCore___lam__1___closed__10);
l_Lean_Meta_substCore___lam__2___closed__0 = _init_l_Lean_Meta_substCore___lam__2___closed__0();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__0);
l_Lean_Meta_substCore___lam__2___closed__1 = _init_l_Lean_Meta_substCore___lam__2___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__1);
l_Lean_Meta_substCore___lam__2___closed__2 = _init_l_Lean_Meta_substCore___lam__2___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__2);
l_Lean_Meta_substCore___lam__2___closed__3 = _init_l_Lean_Meta_substCore___lam__2___closed__3();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__3);
l_Lean_Meta_substCore___lam__2___closed__4 = _init_l_Lean_Meta_substCore___lam__2___closed__4();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__4);
l_Lean_Meta_substCore___lam__2___closed__5 = _init_l_Lean_Meta_substCore___lam__2___closed__5();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__5);
l_Lean_Meta_substCore___lam__2___closed__6 = _init_l_Lean_Meta_substCore___lam__2___closed__6();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__6);
l_Lean_Meta_substCore___lam__2___closed__7 = _init_l_Lean_Meta_substCore___lam__2___closed__7();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__7);
l_Lean_Meta_substCore___lam__2___closed__8 = _init_l_Lean_Meta_substCore___lam__2___closed__8();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__8);
l_Lean_Meta_substCore___lam__2___closed__9 = _init_l_Lean_Meta_substCore___lam__2___closed__9();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__9);
l_Lean_Meta_substCore___lam__2___closed__10 = _init_l_Lean_Meta_substCore___lam__2___closed__10();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__10);
l_Lean_Meta_substCore___lam__2___closed__11 = _init_l_Lean_Meta_substCore___lam__2___closed__11();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__11);
l_Lean_Meta_substCore___lam__2___closed__12 = _init_l_Lean_Meta_substCore___lam__2___closed__12();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__12);
l_Lean_Meta_substCore___lam__2___closed__13 = _init_l_Lean_Meta_substCore___lam__2___closed__13();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__13);
l_Lean_Meta_substCore___lam__2___closed__14 = _init_l_Lean_Meta_substCore___lam__2___closed__14();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__14);
l_Lean_Meta_substCore___lam__2___closed__15 = _init_l_Lean_Meta_substCore___lam__2___closed__15();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__15);
l_Lean_Meta_substCore___lam__2___closed__16 = _init_l_Lean_Meta_substCore___lam__2___closed__16();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__16);
l_Lean_Meta_substCore___lam__2___closed__17 = _init_l_Lean_Meta_substCore___lam__2___closed__17();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__17);
l_Lean_Meta_substCore___lam__2___closed__18 = _init_l_Lean_Meta_substCore___lam__2___closed__18();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__18);
l_Lean_Meta_substCore___lam__2___closed__19 = _init_l_Lean_Meta_substCore___lam__2___closed__19();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__19);
l_Lean_Meta_substCore___lam__2___closed__20 = _init_l_Lean_Meta_substCore___lam__2___closed__20();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__20);
l_Lean_Meta_substCore___lam__2___closed__21 = _init_l_Lean_Meta_substCore___lam__2___closed__21();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__21);
l_Lean_Meta_substCore___lam__2___closed__22 = _init_l_Lean_Meta_substCore___lam__2___closed__22();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__22);
l_Lean_Meta_substCore___lam__2___closed__23 = _init_l_Lean_Meta_substCore___lam__2___closed__23();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__23);
l_Lean_Meta_substCore___lam__2___closed__24 = _init_l_Lean_Meta_substCore___lam__2___closed__24();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__24);
l_Lean_Meta_substCore___lam__2___closed__25 = _init_l_Lean_Meta_substCore___lam__2___closed__25();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__25);
l_Lean_Meta_substCore___lam__2___closed__26 = _init_l_Lean_Meta_substCore___lam__2___closed__26();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__26);
l_Lean_Meta_substCore___lam__2___closed__27 = _init_l_Lean_Meta_substCore___lam__2___closed__27();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__27);
l_Lean_Meta_substCore___lam__2___closed__28 = _init_l_Lean_Meta_substCore___lam__2___closed__28();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__28);
l_Lean_Meta_substCore___lam__2___closed__29 = _init_l_Lean_Meta_substCore___lam__2___closed__29();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__29);
l_Lean_Meta_substCore___lam__2___closed__30 = _init_l_Lean_Meta_substCore___lam__2___closed__30();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__30);
l_Lean_Meta_substCore___lam__2___closed__31 = _init_l_Lean_Meta_substCore___lam__2___closed__31();
lean_mark_persistent(l_Lean_Meta_substCore___lam__2___closed__31);
l_Lean_Meta_heqToEq___lam__0___closed__0 = _init_l_Lean_Meta_heqToEq___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_heqToEq___lam__0___closed__0);
l_Lean_Meta_heqToEq___lam__0___closed__1 = _init_l_Lean_Meta_heqToEq___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_heqToEq___lam__0___closed__1);
l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0___closed__0 = _init_l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lean_PersistentArray_findSomeMAux___at___Lean_PersistentArray_findSomeM_x3f___at___Lean_LocalContext_findDeclM_x3f___at___Lean_Meta_substVar_spec__0_spec__0_spec__0___closed__0);
l_Lean_Meta_substVar___lam__0___closed__0 = _init_l_Lean_Meta_substVar___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_substVar___lam__0___closed__0);
l_Lean_Meta_substVar___lam__0___closed__1 = _init_l_Lean_Meta_substVar___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_substVar___lam__0___closed__1);
l_Lean_Meta_substVar___lam__0___closed__2 = _init_l_Lean_Meta_substVar___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_substVar___lam__0___closed__2);
l_Lean_Meta_substVar___lam__0___closed__3 = _init_l_Lean_Meta_substVar___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_substVar___lam__0___closed__3);
l_Lean_Meta_substVar___lam__0___closed__4 = _init_l_Lean_Meta_substVar___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_substVar___lam__0___closed__4);
l_Lean_Meta_substVar___lam__0___closed__5 = _init_l_Lean_Meta_substVar___lam__0___closed__5();
lean_mark_persistent(l_Lean_Meta_substVar___lam__0___closed__5);
l_Lean_Meta_subst_substEq___lam__0___closed__0 = _init_l_Lean_Meta_subst_substEq___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_subst_substEq___lam__0___closed__0);
l_Lean_Meta_subst_substEq___lam__0___closed__1 = _init_l_Lean_Meta_subst_substEq___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_subst_substEq___lam__0___closed__1);
l_Lean_Meta_subst_substEq___lam__0___closed__2 = _init_l_Lean_Meta_subst_substEq___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_subst_substEq___lam__0___closed__2);
l_Lean_Meta_subst_substEq___lam__0___closed__3 = _init_l_Lean_Meta_subst_substEq___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_subst_substEq___lam__0___closed__3);
l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0 = _init_l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0);
l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Subst___hyg_3853_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Subst___hyg_3853_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Subst___hyg_3853_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Subst___hyg_3853_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Subst___hyg_3853_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Subst___hyg_3853_);
l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Subst___hyg_3853_ = _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Subst___hyg_3853_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Subst___hyg_3853_);
l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Subst___hyg_3853_ = _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Subst___hyg_3853_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Subst___hyg_3853_);
l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Subst___hyg_3853_ = _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Subst___hyg_3853_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Subst___hyg_3853_);
l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Subst___hyg_3853_ = _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Subst___hyg_3853_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Subst___hyg_3853_);
l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Subst___hyg_3853_ = _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Subst___hyg_3853_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Subst___hyg_3853_);
l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Subst___hyg_3853_ = _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Subst___hyg_3853_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Subst___hyg_3853_);
l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Subst___hyg_3853_ = _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Subst___hyg_3853_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Subst___hyg_3853_);
l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Subst___hyg_3853_ = _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Subst___hyg_3853_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Subst___hyg_3853_);
l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Subst___hyg_3853_ = _init_l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Subst___hyg_3853_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Subst___hyg_3853_);
l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Subst___hyg_3853_ = _init_l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Subst___hyg_3853_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Subst___hyg_3853_);
l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Subst___hyg_3853_ = _init_l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Subst___hyg_3853_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Subst___hyg_3853_);
l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Subst___hyg_3853_ = _init_l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Subst___hyg_3853_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Subst___hyg_3853_);
l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Subst___hyg_3853_ = _init_l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Subst___hyg_3853_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Subst___hyg_3853_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_3853_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
