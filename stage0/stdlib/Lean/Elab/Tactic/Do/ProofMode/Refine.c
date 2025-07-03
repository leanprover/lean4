// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Refine
// Imports: Std.Tactic.Do.Syntax Lean.Elab.Tactic.Do.ProofMode.Focus Lean.Elab.Tactic.Do.ProofMode.Assumption Lean.Elab.Tactic.Do.ProofMode.Exact
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2;
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_reprTSyntax___redArg____x40_Init_Meta___hyg_2324_(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__0;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__4;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__7;
static lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__1;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6;
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2;
lean_object* l_Lean_Parser_Tactic_MRefinePat_parse(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17;
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4;
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__1;
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__3;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__16;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18;
static lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__2;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___boxed(lean_object**);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1;
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23;
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21;
lean_object* l_Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__19;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__10;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__0;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__2;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0;
static lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__3;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__23;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13;
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15;
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___boxed(lean_object**);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__2;
lean_object* l_Lean_Expr_consumeMData(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__0;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2;
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__20;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22;
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("binderIdent", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__1;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2;
lean_inc(x_36);
x_38 = l_Lean_Syntax_isOfKind(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_11);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Lean_Syntax_getArg(x_36, x_41);
lean_dec(x_36);
x_43 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4;
lean_inc(x_42);
x_44 = l_Lean_Syntax_isOfKind(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_11);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_st_ref_get(x_10, x_11);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_12 = x_42;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_48;
goto block_35;
}
}
}
case 2:
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
lean_dec(x_1);
x_12 = x_49;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_11;
goto block_35;
}
default: 
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_11);
return x_51;
}
}
block_35:
{
uint8_t x_22; lean_object* x_23; 
x_22 = 0;
x_23 = l_Lean_Elab_Tactic_elabTerm(x_12, x_2, x_22, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pattern does not elaborate to a term to instantiate ψ", 54, 53);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Do", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("SPred", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exists_intro'", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exists", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Neither a conjunction nor an existential quantifier ", 52, 52);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("and_intro", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("could not solve ", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" by assumption", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown hypothesis '", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_ctor_set_tag(x_2, 3);
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_14, x_18);
x_20 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4;
x_21 = l_Lean_Syntax_isOfKind(x_19, x_20);
if (x_21 == 0)
{
lean_ctor_set_tag(x_2, 3);
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = l_Lean_Elab_Tactic_saveState___redArg(x_5, x_7, x_9, x_11, x_12);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_14);
lean_ctor_set_tag(x_2, 2);
lean_inc(x_3);
lean_inc(x_1);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore), 12, 3);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, x_2);
lean_closure_set(x_26, 2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_27 = l_Lean_Elab_Tactic_withoutRecover___redArg(x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_36; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
x_36 = l_Lean_Exception_isInterrupt(x_28);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Exception_isRuntime(x_28);
lean_dec(x_28);
x_30 = x_37;
goto block_35;
}
else
{
lean_dec(x_28);
x_30 = x_36;
goto block_35;
}
block_35:
{
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
x_31 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_24, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_14);
x_2 = x_33;
x_12 = x_32;
goto _start;
}
else
{
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_27;
}
}
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
lean_dec(x_2);
x_39 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2;
lean_inc(x_38);
x_40 = l_Lean_Syntax_isOfKind(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_38);
x_2 = x_41;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_Lean_Syntax_getArg(x_38, x_43);
x_45 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4;
x_46 = l_Lean_Syntax_isOfKind(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_38);
x_2 = x_47;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = l_Lean_Elab_Tactic_saveState___redArg(x_5, x_7, x_9, x_11, x_12);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_38);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_38);
lean_inc(x_3);
lean_inc(x_1);
x_53 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore), 12, 3);
lean_closure_set(x_53, 0, x_1);
lean_closure_set(x_53, 1, x_52);
lean_closure_set(x_53, 2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_54 = l_Lean_Elab_Tactic_withoutRecover___redArg(x_53, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_51);
if (lean_obj_tag(x_54) == 0)
{
lean_dec(x_50);
lean_dec(x_38);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_63; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
x_63 = l_Lean_Exception_isInterrupt(x_55);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = l_Lean_Exception_isRuntime(x_55);
lean_dec(x_55);
x_57 = x_64;
goto block_62;
}
else
{
lean_dec(x_55);
x_57 = x_63;
goto block_62;
}
block_62:
{
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_54);
x_58 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_50, x_57, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_56);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_38);
x_2 = x_60;
x_12 = x_59;
goto _start;
}
else
{
lean_dec(x_56);
lean_dec(x_50);
lean_dec(x_38);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_54;
}
}
}
}
}
}
}
case 1:
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_2, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_66 = x_2;
} else {
 lean_dec_ref(x_2);
 x_66 = lean_box(0);
}
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_67; 
lean_dec(x_66);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_67 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_12);
return x_67;
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
lean_dec(x_66);
x_69 = lean_ctor_get(x_65, 0);
lean_inc(x_69);
lean_dec(x_65);
x_2 = x_69;
goto _start;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_1, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_1, 2);
lean_inc(x_75);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 x_76 = x_1;
} else {
 lean_dec_ref(x_1);
 x_76 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_75);
x_77 = l_Lean_Meta_whnfR(x_75, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_126; lean_object* x_127; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
x_126 = l_Lean_Expr_consumeMData(x_79);
x_127 = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(x_126);
lean_dec(x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_128 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9;
x_129 = lean_unsigned_to_nat(3u);
x_130 = l_Lean_Expr_isAppOfArity(x_79, x_128, x_129);
if (x_130 == 0)
{
lean_dec(x_79);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_131; 
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_66);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_131 = !lean_is_exclusive(x_68);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_132 = lean_ctor_get(x_68, 1);
lean_dec(x_132);
x_133 = lean_ctor_get(x_68, 0);
lean_dec(x_133);
x_134 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11;
x_135 = l_Lean_MessageData_ofExpr(x_75);
lean_ctor_set_tag(x_77, 7);
lean_ctor_set(x_77, 1, x_135);
lean_ctor_set(x_77, 0, x_134);
x_136 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13;
lean_ctor_set_tag(x_68, 7);
lean_ctor_set(x_68, 1, x_136);
lean_ctor_set(x_68, 0, x_77);
x_137 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_68, x_8, x_9, x_10, x_11, x_80);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_68);
x_138 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11;
x_139 = l_Lean_MessageData_ofExpr(x_75);
lean_ctor_set_tag(x_77, 7);
lean_ctor_set(x_77, 1, x_139);
lean_ctor_set(x_77, 0, x_138);
x_140 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13;
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_77);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_141, x_8, x_9, x_10, x_11, x_80);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_free_object(x_77);
lean_dec(x_75);
x_143 = lean_ctor_get(x_127, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
x_81 = x_145;
x_82 = x_146;
x_83 = x_147;
goto block_125;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_free_object(x_77);
lean_dec(x_75);
x_148 = l_Lean_Expr_appFn_x21(x_79);
x_149 = l_Lean_Expr_appFn_x21(x_148);
x_150 = l_Lean_Expr_appArg_x21(x_149);
lean_dec(x_149);
x_151 = l_Lean_Expr_appArg_x21(x_148);
lean_dec(x_148);
x_152 = l_Lean_Expr_appArg_x21(x_79);
lean_dec(x_79);
x_81 = x_150;
x_82 = x_151;
x_83 = x_152;
goto block_125;
}
}
else
{
uint8_t x_153; 
lean_free_object(x_77);
lean_dec(x_79);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_66);
x_153 = !lean_is_exclusive(x_127);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_154 = lean_ctor_get(x_127, 0);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_ctor_get(x_155, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
lean_dec(x_155);
lean_inc(x_157);
lean_inc(x_74);
lean_inc(x_73);
x_159 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_159, 0, x_73);
lean_ctor_set(x_159, 1, x_74);
lean_ctor_set(x_159, 2, x_157);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_160 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(x_159, x_71, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_80);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
lean_inc(x_158);
lean_inc(x_74);
x_163 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_163, 0, x_73);
lean_ctor_set(x_163, 1, x_74);
lean_ctor_set(x_163, 2, x_158);
lean_ctor_set(x_127, 0, x_68);
x_164 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(x_163, x_127, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_162);
if (lean_obj_tag(x_164) == 0)
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_164, 0);
x_167 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16;
x_168 = l_Lean_mkApp6(x_167, x_156, x_74, x_157, x_158, x_161, x_166);
lean_ctor_set(x_164, 0, x_168);
return x_164;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = lean_ctor_get(x_164, 0);
x_170 = lean_ctor_get(x_164, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_164);
x_171 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16;
x_172 = l_Lean_mkApp6(x_171, x_156, x_74, x_157, x_158, x_161, x_169);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_170);
return x_173;
}
}
else
{
lean_dec(x_161);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_74);
return x_164;
}
}
else
{
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_free_object(x_127);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_68);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_160;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_174 = lean_ctor_get(x_127, 0);
lean_inc(x_174);
lean_dec(x_127);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_dec(x_175);
lean_inc(x_177);
lean_inc(x_74);
lean_inc(x_73);
x_179 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_179, 0, x_73);
lean_ctor_set(x_179, 1, x_74);
lean_ctor_set(x_179, 2, x_177);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_180 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(x_179, x_71, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_80);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
lean_inc(x_178);
lean_inc(x_74);
x_183 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_183, 0, x_73);
lean_ctor_set(x_183, 1, x_74);
lean_ctor_set(x_183, 2, x_178);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_68);
x_185 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(x_183, x_184, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_182);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_188 = x_185;
} else {
 lean_dec_ref(x_185);
 x_188 = lean_box(0);
}
x_189 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16;
x_190 = l_Lean_mkApp6(x_189, x_176, x_74, x_177, x_178, x_181, x_186);
if (lean_is_scalar(x_188)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_188;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_187);
return x_191;
}
else
{
lean_dec(x_181);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_74);
return x_185;
}
}
else
{
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_68);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_180;
}
}
}
block_125:
{
lean_object* x_84; lean_object* x_85; 
lean_inc(x_81);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_81);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_85 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm(x_71, x_84, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_80);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1;
x_89 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_88, x_8, x_9, x_10, x_11, x_87);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_dec(x_85);
x_91 = lean_ctor_get(x_86, 0);
lean_inc(x_91);
lean_dec(x_86);
x_92 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2;
lean_inc(x_91);
x_93 = lean_array_push(x_92, x_91);
x_94 = 0;
lean_inc(x_83);
x_95 = l_Lean_Expr_betaRev(x_83, x_93, x_94, x_94);
lean_dec(x_93);
lean_inc(x_74);
if (lean_is_scalar(x_76)) {
 x_96 = lean_alloc_ctor(0, 3, 0);
} else {
 x_96 = x_76;
}
lean_ctor_set(x_96, 0, x_73);
lean_ctor_set(x_96, 1, x_74);
lean_ctor_set(x_96, 2, x_95);
if (lean_is_scalar(x_66)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_66;
}
lean_ctor_set(x_97, 0, x_68);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_98 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(x_96, x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_90);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
lean_inc(x_81);
x_101 = l_Lean_Meta_getLevel(x_81, x_8, x_9, x_10, x_11, x_100);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7;
x_105 = lean_box(0);
if (lean_is_scalar(x_72)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_72;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_Expr_const___override(x_104, x_106);
x_108 = l_Lean_mkApp6(x_107, x_81, x_82, x_74, x_83, x_91, x_99);
lean_ctor_set(x_101, 0, x_108);
return x_101;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_109 = lean_ctor_get(x_101, 0);
x_110 = lean_ctor_get(x_101, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_101);
x_111 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7;
x_112 = lean_box(0);
if (lean_is_scalar(x_72)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_72;
}
lean_ctor_set(x_113, 0, x_109);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_Expr_const___override(x_111, x_113);
x_115 = l_Lean_mkApp6(x_114, x_81, x_82, x_74, x_83, x_91, x_99);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_110);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_dec(x_99);
lean_dec(x_91);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec(x_72);
x_117 = !lean_is_exclusive(x_101);
if (x_117 == 0)
{
return x_101;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_101, 0);
x_119 = lean_ctor_get(x_101, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_101);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_dec(x_91);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_98;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_121 = !lean_is_exclusive(x_85);
if (x_121 == 0)
{
return x_85;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_85, 0);
x_123 = lean_ctor_get(x_85, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_85);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_233; lean_object* x_234; 
x_192 = lean_ctor_get(x_77, 0);
x_193 = lean_ctor_get(x_77, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_77);
x_233 = l_Lean_Expr_consumeMData(x_192);
x_234 = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(x_233);
lean_dec(x_233);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; uint8_t x_237; 
x_235 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9;
x_236 = lean_unsigned_to_nat(3u);
x_237 = l_Lean_Expr_isAppOfArity(x_192, x_235, x_236);
if (x_237 == 0)
{
lean_dec(x_192);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_66);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_238 = x_68;
} else {
 lean_dec_ref(x_68);
 x_238 = lean_box(0);
}
x_239 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11;
x_240 = l_Lean_MessageData_ofExpr(x_75);
x_241 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
x_242 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13;
if (lean_is_scalar(x_238)) {
 x_243 = lean_alloc_ctor(7, 2, 0);
} else {
 x_243 = x_238;
 lean_ctor_set_tag(x_243, 7);
}
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_243, x_8, x_9, x_10, x_11, x_193);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_75);
x_245 = lean_ctor_get(x_234, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 0);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_ctor_get(x_246, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_246, 1);
lean_inc(x_249);
lean_dec(x_246);
x_194 = x_247;
x_195 = x_248;
x_196 = x_249;
goto block_232;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_75);
x_250 = l_Lean_Expr_appFn_x21(x_192);
x_251 = l_Lean_Expr_appFn_x21(x_250);
x_252 = l_Lean_Expr_appArg_x21(x_251);
lean_dec(x_251);
x_253 = l_Lean_Expr_appArg_x21(x_250);
lean_dec(x_250);
x_254 = l_Lean_Expr_appArg_x21(x_192);
lean_dec(x_192);
x_194 = x_252;
x_195 = x_253;
x_196 = x_254;
goto block_232;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_192);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_66);
x_255 = lean_ctor_get(x_234, 0);
lean_inc(x_255);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 x_256 = x_234;
} else {
 lean_dec_ref(x_234);
 x_256 = lean_box(0);
}
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
x_258 = lean_ctor_get(x_255, 0);
lean_inc(x_258);
lean_dec(x_255);
x_259 = lean_ctor_get(x_257, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_257, 1);
lean_inc(x_260);
lean_dec(x_257);
lean_inc(x_259);
lean_inc(x_74);
lean_inc(x_73);
x_261 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_261, 0, x_73);
lean_ctor_set(x_261, 1, x_74);
lean_ctor_set(x_261, 2, x_259);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_262 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(x_261, x_71, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_193);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
lean_inc(x_260);
lean_inc(x_74);
x_265 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_265, 0, x_73);
lean_ctor_set(x_265, 1, x_74);
lean_ctor_set(x_265, 2, x_260);
if (lean_is_scalar(x_256)) {
 x_266 = lean_alloc_ctor(1, 1, 0);
} else {
 x_266 = x_256;
}
lean_ctor_set(x_266, 0, x_68);
x_267 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(x_265, x_266, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_264);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_270 = x_267;
} else {
 lean_dec_ref(x_267);
 x_270 = lean_box(0);
}
x_271 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16;
x_272 = l_Lean_mkApp6(x_271, x_258, x_74, x_259, x_260, x_263, x_268);
if (lean_is_scalar(x_270)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_270;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_269);
return x_273;
}
else
{
lean_dec(x_263);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_74);
return x_267;
}
}
else
{
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_256);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_68);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_262;
}
}
block_232:
{
lean_object* x_197; lean_object* x_198; 
lean_inc(x_194);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_194);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_198 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm(x_71, x_197, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_193);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1;
x_202 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_201, x_8, x_9, x_10, x_11, x_200);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_203 = lean_ctor_get(x_198, 1);
lean_inc(x_203);
lean_dec(x_198);
x_204 = lean_ctor_get(x_199, 0);
lean_inc(x_204);
lean_dec(x_199);
x_205 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2;
lean_inc(x_204);
x_206 = lean_array_push(x_205, x_204);
x_207 = 0;
lean_inc(x_196);
x_208 = l_Lean_Expr_betaRev(x_196, x_206, x_207, x_207);
lean_dec(x_206);
lean_inc(x_74);
if (lean_is_scalar(x_76)) {
 x_209 = lean_alloc_ctor(0, 3, 0);
} else {
 x_209 = x_76;
}
lean_ctor_set(x_209, 0, x_73);
lean_ctor_set(x_209, 1, x_74);
lean_ctor_set(x_209, 2, x_208);
if (lean_is_scalar(x_66)) {
 x_210 = lean_alloc_ctor(1, 1, 0);
} else {
 x_210 = x_66;
}
lean_ctor_set(x_210, 0, x_68);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_211 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(x_209, x_210, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_203);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
lean_inc(x_194);
x_214 = l_Lean_Meta_getLevel(x_194, x_8, x_9, x_10, x_11, x_213);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_217 = x_214;
} else {
 lean_dec_ref(x_214);
 x_217 = lean_box(0);
}
x_218 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7;
x_219 = lean_box(0);
if (lean_is_scalar(x_72)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_72;
}
lean_ctor_set(x_220, 0, x_215);
lean_ctor_set(x_220, 1, x_219);
x_221 = l_Lean_Expr_const___override(x_218, x_220);
x_222 = l_Lean_mkApp6(x_221, x_194, x_195, x_74, x_196, x_204, x_212);
if (lean_is_scalar(x_217)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_217;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_216);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_212);
lean_dec(x_204);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_74);
lean_dec(x_72);
x_224 = lean_ctor_get(x_214, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_214, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_226 = x_214;
} else {
 lean_dec_ref(x_214);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
else
{
lean_dec(x_204);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_211;
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_228 = lean_ctor_get(x_198, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_198, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_230 = x_198;
} else {
 lean_dec_ref(x_198);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
}
}
else
{
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_77;
}
}
}
}
case 2:
{
lean_object* x_274; lean_object* x_275; 
lean_dec(x_3);
x_274 = lean_ctor_get(x_2, 0);
lean_inc(x_274);
lean_dec(x_2);
x_275 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(x_1, x_274, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_275;
}
case 3:
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_276 = lean_ctor_get(x_2, 0);
lean_inc(x_276);
lean_dec(x_2);
x_277 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2;
lean_inc(x_276);
x_278 = l_Lean_Syntax_isOfKind(x_276, x_277);
if (x_278 == 0)
{
lean_object* x_279; 
lean_dec(x_276);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_279 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = lean_ctor_get(x_1, 2);
lean_inc(x_282);
lean_dec(x_1);
x_283 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18;
x_284 = l_Lean_MessageData_ofExpr(x_282);
x_285 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
x_286 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20;
x_287 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
x_288 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_287, x_8, x_9, x_10, x_11, x_281);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_288;
}
else
{
uint8_t x_289; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_289 = !lean_is_exclusive(x_279);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_279, 0);
lean_dec(x_290);
x_291 = lean_ctor_get(x_280, 0);
lean_inc(x_291);
lean_dec(x_280);
lean_ctor_set(x_279, 0, x_291);
return x_279;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_279, 1);
lean_inc(x_292);
lean_dec(x_279);
x_293 = lean_ctor_get(x_280, 0);
lean_inc(x_293);
lean_dec(x_280);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
}
else
{
uint8_t x_295; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_295 = !lean_is_exclusive(x_279);
if (x_295 == 0)
{
return x_279;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_279, 0);
x_297 = lean_ctor_get(x_279, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_279);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
return x_298;
}
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_299 = lean_unsigned_to_nat(0u);
x_300 = l_Lean_Syntax_getArg(x_276, x_299);
lean_dec(x_276);
x_301 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4;
lean_inc(x_300);
x_302 = l_Lean_Syntax_isOfKind(x_300, x_301);
if (x_302 == 0)
{
lean_object* x_303; 
lean_dec(x_300);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_303 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_306 = lean_ctor_get(x_1, 2);
lean_inc(x_306);
lean_dec(x_1);
x_307 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18;
x_308 = l_Lean_MessageData_ofExpr(x_306);
x_309 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
x_310 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20;
x_311 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
x_312 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_311, x_8, x_9, x_10, x_11, x_305);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_312;
}
else
{
uint8_t x_313; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_313 = !lean_is_exclusive(x_303);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_303, 0);
lean_dec(x_314);
x_315 = lean_ctor_get(x_304, 0);
lean_inc(x_315);
lean_dec(x_304);
lean_ctor_set(x_303, 0, x_315);
return x_303;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_303, 1);
lean_inc(x_316);
lean_dec(x_303);
x_317 = lean_ctor_get(x_304, 0);
lean_inc(x_317);
lean_dec(x_304);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_316);
return x_318;
}
}
}
else
{
uint8_t x_319; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_319 = !lean_is_exclusive(x_303);
if (x_319 == 0)
{
return x_303;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_303, 0);
x_321 = lean_ctor_get(x_303, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_303);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
}
else
{
lean_object* x_323; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_300);
x_323 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(x_1, x_300, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_326 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22;
x_327 = l_Lean_Syntax_reprTSyntax___redArg____x40_Init_Meta___hyg_2324_(x_300);
x_328 = l_Lean_MessageData_ofFormat(x_327);
x_329 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_329, 0, x_326);
lean_ctor_set(x_329, 1, x_328);
x_330 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24;
x_331 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
x_332 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_331, x_8, x_9, x_10, x_11, x_325);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_332;
}
else
{
uint8_t x_333; 
lean_dec(x_300);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_333 = !lean_is_exclusive(x_323);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_ctor_get(x_323, 0);
lean_dec(x_334);
x_335 = lean_ctor_get(x_324, 0);
lean_inc(x_335);
lean_dec(x_324);
lean_ctor_set(x_323, 0, x_335);
return x_323;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_323, 1);
lean_inc(x_336);
lean_dec(x_323);
x_337 = lean_ctor_get(x_324, 0);
lean_inc(x_337);
lean_dec(x_324);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_336);
return x_338;
}
}
}
else
{
uint8_t x_339; 
lean_dec(x_300);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_339 = !lean_is_exclusive(x_323);
if (x_339 == 0)
{
return x_323;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_323, 0);
x_341 = lean_ctor_get(x_323, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_323);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
return x_342;
}
}
}
}
}
default: 
{
lean_object* x_343; lean_object* x_344; 
x_343 = lean_ctor_get(x_2, 0);
lean_inc(x_343);
lean_dec(x_2);
x_344 = lean_apply_11(x_3, x_1, x_343, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_344;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_13 = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(x_2);
x_14 = l_Lean_Syntax_getId(x_3);
x_15 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_13, x_14, x_8, x_9, x_10, x_11, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_take(x_1, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Expr_mvarId_x21(x_16);
x_22 = lean_array_push(x_19, x_21);
x_23 = lean_st_ref_set(x_1, x_22, x_20);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_16);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_st_mk_ref(x_1, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0___boxed), 12, 1);
lean_closure_set(x_17, 0, x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_6);
x_18 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(x_2, x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0___redArg(x_4, x_19, x_10, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_15, x_22);
lean_dec(x_15);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_array_to_list(x_24);
x_27 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_26, x_6, x_9, x_10, x_11, x_12, x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mrefine", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_MRefinePat_parse), 3, 1);
lean_closure_set(x_16, 0, x_15);
lean_inc(x_8);
x_17 = l_Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0___redArg(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_3, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_23 = l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar(x_21, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4;
lean_inc(x_26);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1), 13, 4);
lean_closure_set(x_29, 0, x_28);
lean_closure_set(x_29, 1, x_27);
lean_closure_set(x_29, 2, x_18);
lean_closure_set(x_29, 3, x_26);
x_30 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_26, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_20);
if (x_35 == 0)
{
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_17, 0);
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_17);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ProofMode", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabMRefine", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__2;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1;
x_5 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1;
x_6 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0;
x_7 = l_Lean_Name_mkStr6(x_6, x_5, x_4, x_3, x_2, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__4;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mrefinePat⌜_⌝", 17, 13);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⌜", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⌝", 3, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_get(x_8, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_7, 5);
x_17 = lean_array_uget(x_6, x_5);
x_18 = lean_box(0);
x_19 = lean_array_uset(x_6, x_5, x_18);
x_20 = 0;
x_21 = l_Lean_SourceInfo_fromRef(x_16, x_20);
x_22 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__0;
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_22);
x_24 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1;
lean_inc(x_21);
lean_ctor_set_tag(x_12, 2);
lean_ctor_set(x_12, 1, x_24);
lean_ctor_set(x_12, 0, x_21);
x_25 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2;
lean_inc(x_21);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Syntax_node3(x_21, x_23, x_12, x_17, x_26);
x_28 = 1;
x_29 = lean_usize_add(x_5, x_28);
x_30 = lean_array_uset(x_19, x_5, x_27);
x_5 = x_29;
x_6 = x_30;
x_9 = x_14;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_dec(x_12);
x_33 = lean_ctor_get(x_7, 5);
x_34 = lean_array_uget(x_6, x_5);
x_35 = lean_box(0);
x_36 = lean_array_uset(x_6, x_5, x_35);
x_37 = 0;
x_38 = l_Lean_SourceInfo_fromRef(x_33, x_37);
x_39 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__0;
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_40 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_39);
x_41 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1;
lean_inc(x_38);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2;
lean_inc(x_38);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Syntax_node3(x_38, x_40, x_42, x_34, x_44);
x_46 = 1;
x_47 = lean_usize_add(x_5, x_46);
x_48 = lean_array_uset(x_36, x_5, x_45);
x_5 = x_47;
x_6 = x_48;
x_9 = x_32;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_15, x_16);
return x_17;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mrefinePat⟨_⟩", 17, 13);
return x_1;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⟨", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mrefinePats", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⟩", 3, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
uint8_t x_19; 
x_19 = lean_usize_dec_eq(x_7, x_8);
if (x_19 == 0)
{
lean_object* x_20; 
lean_inc(x_1);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_20 = lean_apply_9(x_1, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_17, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = 1;
x_28 = lean_usize_sub(x_7, x_27);
x_29 = lean_array_uget(x_6, x_28);
x_30 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__0;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_31 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_30);
x_32 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__1;
lean_inc(x_21);
lean_ctor_set_tag(x_23, 2);
lean_ctor_set(x_23, 1, x_32);
lean_ctor_set(x_23, 0, x_21);
x_33 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__2;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_33);
x_35 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__4;
lean_inc(x_5);
lean_inc(x_21);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_5);
lean_inc(x_21);
x_37 = l_Lean_Syntax_node3(x_21, x_35, x_29, x_36, x_9);
lean_inc(x_21);
x_38 = l_Lean_Syntax_node1(x_21, x_34, x_37);
x_39 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__5;
lean_inc(x_21);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_21);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Syntax_node3(x_21, x_31, x_23, x_38, x_40);
x_7 = x_28;
x_9 = x_41;
x_18 = x_25;
goto _start;
}
else
{
lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_43 = lean_ctor_get(x_23, 1);
lean_inc(x_43);
lean_dec(x_23);
x_44 = 1;
x_45 = lean_usize_sub(x_7, x_44);
x_46 = lean_array_uget(x_6, x_45);
x_47 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__0;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_48 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_47);
x_49 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__1;
lean_inc(x_21);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_21);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__2;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_52 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_51);
x_53 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__4;
lean_inc(x_5);
lean_inc(x_21);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_21);
lean_ctor_set(x_54, 1, x_5);
lean_inc(x_21);
x_55 = l_Lean_Syntax_node3(x_21, x_53, x_46, x_54, x_9);
lean_inc(x_21);
x_56 = l_Lean_Syntax_node1(x_21, x_52, x_55);
x_57 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__5;
lean_inc(x_21);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_21);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Syntax_node3(x_21, x_48, x_50, x_56, x_58);
x_7 = x_45;
x_9 = x_59;
x_18 = x_43;
goto _start;
}
}
else
{
uint8_t x_61; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_20);
if (x_61 == 0)
{
return x_20;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_20, 0);
x_63 = lean_ctor_get(x_20, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_20);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_9);
lean_ctor_set(x_65, 1, x_18);
return x_65;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; 
x_20 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mexists", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__0;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("paren", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__2;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__5;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__7;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(";", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticTry_", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__10;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("try", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("massumption", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mrefinePat\?_", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__16;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\?", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hole", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__20;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__19;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0;
x_12 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0;
x_13 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1;
x_14 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1;
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_19 = l_Lean_Syntax_getArgs(x_18);
lean_dec(x_18);
x_20 = l_Lean_Syntax_TSepArray_getElems___redArg(x_19);
lean_dec(x_19);
x_21 = lean_array_size(x_20);
x_22 = 0;
x_23 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(x_11, x_12, x_13, x_21, x_22, x_20, x_8, x_9, x_10);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = lean_st_ref_get(x_9, x_25);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_8, 5);
lean_inc(x_30);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___lam__0___boxed), 9, 0);
x_136 = lean_unsigned_to_nat(0u);
x_137 = 0;
x_138 = l_Lean_SourceInfo_fromRef(x_30, x_137);
lean_dec(x_30);
x_139 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17;
x_140 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18;
lean_inc(x_138);
x_141 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2;
x_143 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21;
x_144 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22;
lean_inc(x_138);
x_145 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_145, 0, x_138);
lean_ctor_set(x_145, 1, x_144);
lean_inc(x_138);
x_146 = l_Lean_Syntax_node1(x_138, x_143, x_145);
lean_inc(x_138);
x_147 = l_Lean_Syntax_node1(x_138, x_142, x_146);
x_148 = l_Lean_Syntax_node2(x_138, x_139, x_141, x_147);
x_149 = lean_array_get_size(x_24);
x_150 = lean_nat_dec_lt(x_136, x_149);
if (x_150 == 0)
{
lean_dec(x_149);
lean_dec(x_31);
lean_dec(x_24);
x_32 = x_148;
x_33 = x_28;
goto block_135;
}
else
{
lean_object* x_151; size_t x_152; lean_object* x_153; 
x_151 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__23;
x_152 = lean_usize_of_nat(x_149);
lean_dec(x_149);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_153 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg(x_31, x_11, x_12, x_13, x_151, x_24, x_152, x_22, x_148, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
lean_dec(x_24);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_32 = x_154;
x_33 = x_155;
goto block_135;
}
else
{
uint8_t x_156; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_156 = !lean_is_exclusive(x_153);
if (x_156 == 0)
{
return x_153;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_153, 0);
x_158 = lean_ctor_get(x_153, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_153);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
block_135:
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___lam__0(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
x_38 = lean_st_ref_get(x_9, x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_40 = lean_ctor_get(x_38, 1);
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
x_42 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3;
x_43 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4;
lean_inc(x_36);
lean_ctor_set_tag(x_38, 2);
lean_ctor_set(x_38, 1, x_43);
lean_ctor_set(x_38, 0, x_36);
x_44 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6;
x_45 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8;
x_46 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__4;
x_47 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2;
x_48 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3;
lean_inc(x_36);
lean_ctor_set_tag(x_34, 2);
lean_ctor_set(x_34, 1, x_47);
lean_inc(x_36);
x_49 = l_Lean_Syntax_node2(x_36, x_48, x_34, x_32);
x_50 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9;
lean_inc(x_36);
if (lean_is_scalar(x_29)) {
 x_51 = lean_alloc_ctor(2, 2, 0);
} else {
 x_51 = x_29;
 lean_ctor_set_tag(x_51, 2);
}
lean_ctor_set(x_51, 0, x_36);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11;
x_53 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12;
lean_inc(x_36);
if (lean_is_scalar(x_26)) {
 x_54 = lean_alloc_ctor(2, 2, 0);
} else {
 x_54 = x_26;
 lean_ctor_set_tag(x_54, 2);
}
lean_ctor_set(x_54, 0, x_36);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13;
x_56 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14;
lean_inc(x_36);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_36);
lean_ctor_set(x_57, 1, x_55);
lean_inc(x_36);
x_58 = l_Lean_Syntax_node1(x_36, x_56, x_57);
lean_inc(x_36);
x_59 = l_Lean_Syntax_node1(x_36, x_46, x_58);
lean_inc(x_36);
x_60 = l_Lean_Syntax_node1(x_36, x_45, x_59);
lean_inc(x_36);
x_61 = l_Lean_Syntax_node1(x_36, x_44, x_60);
lean_inc(x_36);
x_62 = l_Lean_Syntax_node2(x_36, x_52, x_54, x_61);
lean_inc(x_36);
x_63 = l_Lean_Syntax_node3(x_36, x_46, x_49, x_51, x_62);
lean_inc(x_36);
x_64 = l_Lean_Syntax_node1(x_36, x_45, x_63);
lean_inc(x_36);
x_65 = l_Lean_Syntax_node1(x_36, x_44, x_64);
x_66 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15;
lean_inc(x_36);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_36);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Syntax_node3(x_36, x_42, x_38, x_65, x_67);
x_69 = l_Lean_Elab_Tactic_evalTactic(x_68, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_40);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_70 = lean_ctor_get(x_38, 1);
lean_inc(x_70);
lean_dec(x_38);
x_71 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3;
x_72 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4;
lean_inc(x_36);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_36);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6;
x_75 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8;
x_76 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__4;
x_77 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2;
x_78 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3;
lean_inc(x_36);
lean_ctor_set_tag(x_34, 2);
lean_ctor_set(x_34, 1, x_77);
lean_inc(x_36);
x_79 = l_Lean_Syntax_node2(x_36, x_78, x_34, x_32);
x_80 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9;
lean_inc(x_36);
if (lean_is_scalar(x_29)) {
 x_81 = lean_alloc_ctor(2, 2, 0);
} else {
 x_81 = x_29;
 lean_ctor_set_tag(x_81, 2);
}
lean_ctor_set(x_81, 0, x_36);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11;
x_83 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12;
lean_inc(x_36);
if (lean_is_scalar(x_26)) {
 x_84 = lean_alloc_ctor(2, 2, 0);
} else {
 x_84 = x_26;
 lean_ctor_set_tag(x_84, 2);
}
lean_ctor_set(x_84, 0, x_36);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13;
x_86 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14;
lean_inc(x_36);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_36);
lean_ctor_set(x_87, 1, x_85);
lean_inc(x_36);
x_88 = l_Lean_Syntax_node1(x_36, x_86, x_87);
lean_inc(x_36);
x_89 = l_Lean_Syntax_node1(x_36, x_76, x_88);
lean_inc(x_36);
x_90 = l_Lean_Syntax_node1(x_36, x_75, x_89);
lean_inc(x_36);
x_91 = l_Lean_Syntax_node1(x_36, x_74, x_90);
lean_inc(x_36);
x_92 = l_Lean_Syntax_node2(x_36, x_82, x_84, x_91);
lean_inc(x_36);
x_93 = l_Lean_Syntax_node3(x_36, x_76, x_79, x_81, x_92);
lean_inc(x_36);
x_94 = l_Lean_Syntax_node1(x_36, x_75, x_93);
lean_inc(x_36);
x_95 = l_Lean_Syntax_node1(x_36, x_74, x_94);
x_96 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15;
lean_inc(x_36);
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_36);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Syntax_node3(x_36, x_71, x_73, x_95, x_97);
x_99 = l_Lean_Elab_Tactic_evalTactic(x_98, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_70);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_100 = lean_ctor_get(x_34, 0);
x_101 = lean_ctor_get(x_34, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_34);
x_102 = lean_st_ref_get(x_9, x_101);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3;
x_106 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4;
lean_inc(x_100);
if (lean_is_scalar(x_104)) {
 x_107 = lean_alloc_ctor(2, 2, 0);
} else {
 x_107 = x_104;
 lean_ctor_set_tag(x_107, 2);
}
lean_ctor_set(x_107, 0, x_100);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6;
x_109 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8;
x_110 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__4;
x_111 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2;
x_112 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3;
lean_inc(x_100);
x_113 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_113, 0, x_100);
lean_ctor_set(x_113, 1, x_111);
lean_inc(x_100);
x_114 = l_Lean_Syntax_node2(x_100, x_112, x_113, x_32);
x_115 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9;
lean_inc(x_100);
if (lean_is_scalar(x_29)) {
 x_116 = lean_alloc_ctor(2, 2, 0);
} else {
 x_116 = x_29;
 lean_ctor_set_tag(x_116, 2);
}
lean_ctor_set(x_116, 0, x_100);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11;
x_118 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12;
lean_inc(x_100);
if (lean_is_scalar(x_26)) {
 x_119 = lean_alloc_ctor(2, 2, 0);
} else {
 x_119 = x_26;
 lean_ctor_set_tag(x_119, 2);
}
lean_ctor_set(x_119, 0, x_100);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13;
x_121 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14;
lean_inc(x_100);
x_122 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_122, 0, x_100);
lean_ctor_set(x_122, 1, x_120);
lean_inc(x_100);
x_123 = l_Lean_Syntax_node1(x_100, x_121, x_122);
lean_inc(x_100);
x_124 = l_Lean_Syntax_node1(x_100, x_110, x_123);
lean_inc(x_100);
x_125 = l_Lean_Syntax_node1(x_100, x_109, x_124);
lean_inc(x_100);
x_126 = l_Lean_Syntax_node1(x_100, x_108, x_125);
lean_inc(x_100);
x_127 = l_Lean_Syntax_node2(x_100, x_117, x_119, x_126);
lean_inc(x_100);
x_128 = l_Lean_Syntax_node3(x_100, x_110, x_114, x_116, x_127);
lean_inc(x_100);
x_129 = l_Lean_Syntax_node1(x_100, x_109, x_128);
lean_inc(x_100);
x_130 = l_Lean_Syntax_node1(x_100, x_108, x_129);
x_131 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15;
lean_inc(x_100);
x_132 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_132, 0, x_100);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_Syntax_node3(x_100, x_105, x_107, x_130, x_132);
x_134 = l_Lean_Elab_Tactic_evalTactic(x_133, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_103);
return x_134;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0(x_1, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___boxed(lean_object** _args) {
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
_start:
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_20 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_21 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_19, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_6);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___boxed(lean_object** _args) {
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
_start:
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_21 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_22 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_20, x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_7);
lean_dec(x_2);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabMExists", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__0;
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__2;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1;
x_5 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1;
x_6 = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0;
x_7 = l_Lean_Name_mkStr6(x_6, x_5, x_4, x_3, x_2, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0;
x_3 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1;
x_4 = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Std_Tactic_Do_Syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_Do_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Exact(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0 = _init_l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0);
l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__1 = _init_l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__1);
l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2 = _init_l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2);
l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__3 = _init_l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__3);
l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4 = _init_l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23);
l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24 = _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24);
l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0);
l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1);
l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2);
l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3);
l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4);
l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0);
l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1);
l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__2 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__2);
l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3);
l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__4 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__4);
if (builtin) {res = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__0 = _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__0();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__0);
l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1 = _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1);
l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2 = _init_l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2);
l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__0 = _init_l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__0();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__0);
l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__1 = _init_l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__1();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__1);
l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__2 = _init_l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__2();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__2);
l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__3 = _init_l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__3();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__3);
l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__4 = _init_l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__4();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__4);
l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__5 = _init_l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__5();
lean_mark_persistent(l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___redArg___closed__5);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__0 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__0);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__2 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__2);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__5 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__5);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__7 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__7);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__10 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__10);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__16 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__16();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__16);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__19 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__19();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__19);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__20 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__20();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__20);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__23 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__23();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__23);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__0 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__0);
l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1 = _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1);
if (builtin) {res = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
