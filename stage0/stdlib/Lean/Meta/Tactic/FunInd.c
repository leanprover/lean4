// Lean compiler output
// Module: Lean.Meta.Tactic.FunInd
// Imports: Lean.Meta.Basic Lean.Meta.Match.MatcherApp.Transform Lean.Meta.Check Lean.Meta.Tactic.Cleanup Lean.Meta.Tactic.Subst Lean.Meta.Injective Lean.Meta.ArgsPacker Lean.Elab.PreDefinition.WF.Eqns Lean.Elab.Command
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionCase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__1;
lean_object* l_Lean_throwError___at_Lean_Meta_collectForwardDeps___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_buildInductionBody___closed__4;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_deriveUnaryInduction___closed__1;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__6;
static lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__5;
lean_object* l_ReaderT_instMonadFunctorReaderT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_curryParam___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__4;
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__7;
static lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__5;
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__1___closed__1;
extern lean_object* l_Lean_Elab_WF_instInhabitedEqnInfo;
static lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__3;
static lean_object* l_Array_mapIdxM_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__7___closed__1;
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__8;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_deriveUnaryInduction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_buildInductionBody___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__1;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isDIte(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Tactic_FunInd_substVarAfter___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_findFixF___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_substVarAfter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__8___closed__1;
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__14;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_substVarAfter___spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__11(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__7;
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__8___closed__1;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_deduplicateIHs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_maskArray___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__6;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revertAfter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__1;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__4;
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__20;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__2;
static lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__3;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_assertIHs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__18;
static lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__4;
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__4(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__3;
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Tactic_FunInd_substVarAfter___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Tactic_FunInd_collectIHs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__9(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_elabDeriveInduction___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_deriveUnpackedInduction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_substVarAfter___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Tactic_FunInd_mkLambdaFVarsMasked___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__3;
static lean_object* l_Lean_Tactic_FunInd_deriveInduction___closed__1;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__17;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_assertIHs___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_elimOptParam___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_findFixF(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Tactic_FunInd_substVarAfter___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__7___closed__1;
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_buildInductionCase___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_buildInductionBody___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_removeLamda___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_buildInductionBody___closed__1;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__7;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__1;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_WF_eqnInfoExt;
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__16___closed__1;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_maskArray(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deduplicateIHs___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__2;
static lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__8___closed__2;
static lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deriveUnpackedInduction___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_substVarAfter___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__4;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_substVarAfter___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Tactic_FunInd_collectIHs___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Tactic_FunInd_substVarAfter___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_Tactic_FunInd_collectIHs___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___boxed(lean_object**);
static lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__1;
lean_object* l_Array_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__10(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_assertIHs___spec__1___closed__1;
lean_object* l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_panic___at___private_Lean_Meta_WHNF_0__Lean_Meta_cache___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Meta_whnfCore_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__3;
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__11;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_buildInductionCase___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__11___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__10;
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__19;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__1(lean_object*);
uint8_t l_Array_contains___at_Lean_Elab_Term_collectUnassignedMVars_go___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__7;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__2;
static lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__2;
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProjAndN(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__2;
static lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__2;
static lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__8___closed__2;
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionCase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadExceptOfReaderT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLiftReaderT(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3___closed__1;
static lean_object* l_Lean_Tactic_FunInd_deduplicateIHs___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__11;
static lean_object* l_Lean_Tactic_FunInd_removeLamda___rarg___closed__3;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__4;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__5;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__2;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__4;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_deduplicateIHs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__3;
lean_object* l_Lean_FVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_findFixF___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__10___closed__1;
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__13;
lean_object* l_Lean_log___at_Lean_Meta_computeSynthOrder___spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__7___closed__2;
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__1;
static lean_object* l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__2;
lean_object* l_Lean_Meta_ArgsPacker_curry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__4;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__3;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_transform(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___closed__2;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_maskArray___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_substVarAfter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
static lean_object* l_Lean_Tactic_FunInd_buildInductionBody___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___closed__1;
static lean_object* l_panic___at_Lean_Tactic_FunInd_collectIHs___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
static lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__7___closed__2;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__3;
static lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__4;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_deriveUnaryInduction___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__9;
extern lean_object* l_Lean_Meta_instMonadMetaM;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Tactic_FunInd_foldCalls___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_deriveUnaryInduction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__7___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deduplicateIHs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Tactic_FunInd_buildInductionBody___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Tactic_FunInd_mkLambdaFVarsMasked___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__11___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___boxed(lean_object**);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__8;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_LMVarId_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAndIntroN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySubstVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__1;
lean_object* l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__6;
static lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__4;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__5;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__5;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__5;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Tactic_FunInd_foldCalls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVarOf(lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__1;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__3;
lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_assertIHs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__1;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__2;
lean_object* l_Lean_instMonadQuotation___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__2;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_deriveInduction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__2;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
static lean_object* l_Lean_Tactic_FunInd_buildInductionCase___closed__1;
static lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__10;
lean_object* l_Lean_instAddErrorMessageContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__12;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_buildInductionBody___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__6;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_elabDeriveInduction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_mkLambdaFVarsMasked(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__6;
static lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_buildInductionCase___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Tactic_FunInd_collectIHs___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Tactic_FunInd_mkLambdaFVarsMasked___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__1;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Tactic_FunInd_buildInductionBody___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__4;
lean_object* l_StateRefT_x27_lift(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_maskArray___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Tactic_FunInd_collectIHs___spec__5(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__4;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Tactic_FunInd_collectIHs___spec__6(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_elabDeriveInduction(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__1;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__7;
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__16;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_elabDeriveInduction___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_deriveUnaryInduction___closed__2;
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__5;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__9___closed__1;
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__15;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__4;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__7;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deriveUnpackedInduction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__2;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__4;
lean_object* l_Lean_Meta_elimOptParam___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__2;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__3;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_findFixF___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_removeLamda___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_maskArray___rarg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__6;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__11(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Tactic_FunInd_mkLambdaFVarsMasked___spec__1___closed__1;
static lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__9;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__2;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__7___closed__1;
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__6;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_removeLamda(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__3;
static lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ArgsPacker_unpack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deriveUnpackedInduction___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
static lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__11;
static lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__8;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Expr_letFun_x3f(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_removeLamda___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_substVarAfter___spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_deriveUnaryInduction___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Tactic_FunInd_substVarAfter___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deriveUnpackedInduction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_substVarAfter___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Tactic_FunInd_substVarAfter___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__2___closed__1;
static lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__8___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_maskArray___spec__1___rarg(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__3;
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_findFixF___spec__1(lean_object*);
static lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__12___closed__1;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__1;
static lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__10___closed__1;
lean_object* l_StateRefT_x27_instMonadExceptOfStateRefT_x27___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__11___closed__1;
static lean_object* l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__9;
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_buildInductionBody___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__5___closed__2;
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_Tactic_FunInd_collectIHs___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__3___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__4___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__5___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__6___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__7___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__8___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__9___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__10___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__11___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_removeLamda___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("removeLamda: expected lambda, got ", 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_removeLamda___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_removeLamda___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_removeLamda___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_whnfD(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_MessageData_ofExpr(x_1);
x_12 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__2;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__1___rarg(x_15, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
case 1:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_2);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = l_Lean_MessageData_ofExpr(x_1);
x_19 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__2___rarg(x_22, x_3, x_4, x_5, x_6, x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_23;
}
case 2:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_2);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_dec(x_8);
x_25 = l_Lean_MessageData_ofExpr(x_1);
x_26 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__2;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__3___rarg(x_29, x_3, x_4, x_5, x_6, x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_30;
}
case 3:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
lean_dec(x_2);
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_dec(x_8);
x_32 = l_Lean_MessageData_ofExpr(x_1);
x_33 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__2;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__4___rarg(x_36, x_3, x_4, x_5, x_6, x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_37;
}
case 4:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_9);
lean_dec(x_2);
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
lean_dec(x_8);
x_39 = l_Lean_MessageData_ofExpr(x_1);
x_40 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__2;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__5___rarg(x_43, x_3, x_4, x_5, x_6, x_38);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_44;
}
case 5:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_9);
lean_dec(x_2);
x_45 = lean_ctor_get(x_8, 1);
lean_inc(x_45);
lean_dec(x_8);
x_46 = l_Lean_MessageData_ofExpr(x_1);
x_47 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__2;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__6___rarg(x_50, x_3, x_4, x_5, x_6, x_45);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_51;
}
case 6:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_1);
x_52 = lean_ctor_get(x_8, 1);
lean_inc(x_52);
lean_dec(x_8);
x_53 = lean_ctor_get(x_9, 2);
lean_inc(x_53);
lean_dec(x_9);
x_54 = l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___rarg(x_6, x_52);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_55);
x_57 = l_Lean_Expr_fvar___override(x_55);
x_58 = lean_expr_instantiate1(x_53, x_57);
lean_dec(x_57);
lean_dec(x_53);
x_59 = lean_apply_7(x_2, x_55, x_58, x_3, x_4, x_5, x_6, x_56);
return x_59;
}
case 7:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_9);
lean_dec(x_2);
x_60 = lean_ctor_get(x_8, 1);
lean_inc(x_60);
lean_dec(x_8);
x_61 = l_Lean_MessageData_ofExpr(x_1);
x_62 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__2;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__7___rarg(x_65, x_3, x_4, x_5, x_6, x_60);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_66;
}
case 8:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_9);
lean_dec(x_2);
x_67 = lean_ctor_get(x_8, 1);
lean_inc(x_67);
lean_dec(x_8);
x_68 = l_Lean_MessageData_ofExpr(x_1);
x_69 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__2;
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__8___rarg(x_72, x_3, x_4, x_5, x_6, x_67);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_73;
}
case 9:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_9);
lean_dec(x_2);
x_74 = lean_ctor_get(x_8, 1);
lean_inc(x_74);
lean_dec(x_8);
x_75 = l_Lean_MessageData_ofExpr(x_1);
x_76 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__2;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__9___rarg(x_79, x_3, x_4, x_5, x_6, x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_80;
}
case 10:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_9);
lean_dec(x_2);
x_81 = lean_ctor_get(x_8, 1);
lean_inc(x_81);
lean_dec(x_8);
x_82 = l_Lean_MessageData_ofExpr(x_1);
x_83 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__2;
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__10___rarg(x_86, x_3, x_4, x_5, x_6, x_81);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_87;
}
default: 
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_9);
lean_dec(x_2);
x_88 = lean_ctor_get(x_8, 1);
lean_inc(x_88);
lean_dec(x_8);
x_89 = l_Lean_MessageData_ofExpr(x_1);
x_90 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__2;
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__11___rarg(x_93, x_3, x_4, x_5, x_6, x_88);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_8);
if (x_95 == 0)
{
return x_8;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_8, 0);
x_97 = lean_ctor_get(x_8, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_8);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_removeLamda(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_removeLamda___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__7___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__8___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__9___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__10___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Tactic_FunInd_removeLamda___spec__11___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Tactic_FunInd_foldCalls___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Expr_isFVarOf(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_expr_instantiate1(x_1, x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
x_15 = lean_array_push(x_14, x_4);
x_16 = 0;
x_17 = 1;
x_18 = 1;
x_19 = l_Lean_Meta_mkLambdaFVars(x_15, x_12, x_16, x_17, x_18, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_expr_instantiate1(x_1, x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
x_15 = lean_array_push(x_14, x_4);
x_16 = 0;
x_17 = 1;
x_18 = 1;
x_19 = l_Lean_Meta_mkForallFVars(x_15, x_12, x_16, x_17, x_18, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Meta.Tactic.FunInd", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Tactic.FunInd.foldCalls", 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__1;
x_2 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__2;
x_3 = lean_unsigned_to_nat(245u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("collectIHs: cannot eliminate unsaturated call to induction hypothesis", 69);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__6;
x_11 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
case 5:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_Expr_app___override(x_15, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = l_Lean_Expr_app___override(x_15, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_15);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
case 6:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_37 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_34, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_foldCalls___lambda__1___boxed), 9, 3);
lean_closure_set(x_40, 0, x_35);
lean_closure_set(x_40, 1, x_2);
lean_closure_set(x_40, 2, x_3);
x_41 = 0;
x_42 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_33, x_36, x_38, x_40, x_41, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_42);
if (x_47 == 0)
{
return x_42;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_42, 0);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_42);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_37);
if (x_51 == 0)
{
return x_37;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_37, 0);
x_53 = lean_ctor_get(x_37, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_37);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
case 7:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_1, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 2);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_59 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_56, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_foldCalls___lambda__2___boxed), 9, 3);
lean_closure_set(x_62, 0, x_57);
lean_closure_set(x_62, 1, x_2);
lean_closure_set(x_62, 2, x_3);
x_63 = 0;
x_64 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_55, x_58, x_60, x_62, x_63, x_5, x_6, x_7, x_8, x_61);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
return x_64;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_64);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_64);
if (x_69 == 0)
{
return x_64;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_64, 0);
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_64);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_59);
if (x_73 == 0)
{
return x_59;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_59, 0);
x_75 = lean_ctor_get(x_59, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_59);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
case 8:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_1, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_1, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_1, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_1, 3);
lean_inc(x_80);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_81 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_78, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_84 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_79, x_5, x_6, x_7, x_8, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_foldCalls___lambda__1___boxed), 9, 3);
lean_closure_set(x_87, 0, x_80);
lean_closure_set(x_87, 1, x_2);
lean_closure_set(x_87, 2, x_3);
x_88 = 0;
x_89 = l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1___rarg(x_77, x_82, x_85, x_87, x_88, x_5, x_6, x_7, x_8, x_86);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
return x_89;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_89);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
else
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_89);
if (x_94 == 0)
{
return x_89;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_89, 0);
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_89);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_84);
if (x_98 == 0)
{
return x_84;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_84, 0);
x_100 = lean_ctor_get(x_84, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_84);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_102 = !lean_is_exclusive(x_81);
if (x_102 == 0)
{
return x_81;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_81, 0);
x_104 = lean_ctor_get(x_81, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_81);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
case 10:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_1, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_1, 1);
lean_inc(x_107);
lean_dec(x_1);
x_108 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_107, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = l_Lean_Expr_mdata___override(x_106, x_110);
lean_ctor_set(x_108, 0, x_111);
return x_108;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_108, 0);
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_108);
x_114 = l_Lean_Expr_mdata___override(x_106, x_112);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
uint8_t x_116; 
lean_dec(x_106);
x_116 = !lean_is_exclusive(x_108);
if (x_116 == 0)
{
return x_108;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_108, 0);
x_118 = lean_ctor_get(x_108, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_108);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
case 11:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_1, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_1, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_1, 2);
lean_inc(x_122);
lean_dec(x_1);
x_123 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_122, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = l_Lean_Expr_proj___override(x_120, x_121, x_125);
lean_ctor_set(x_123, 0, x_126);
return x_123;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_123, 0);
x_128 = lean_ctor_get(x_123, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_123);
x_129 = l_Lean_Expr_proj___override(x_120, x_121, x_127);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
else
{
uint8_t x_131; 
lean_dec(x_121);
lean_dec(x_120);
x_131 = !lean_is_exclusive(x_123);
if (x_131 == 0)
{
return x_123;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_123, 0);
x_133 = lean_ctor_get(x_123, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_123);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
default: 
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_135 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__4;
x_136 = l_panic___at_Lean_Meta_whnfCore_go___spec__1(x_135, x_5, x_6, x_7, x_8, x_9);
return x_136;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_expr_instantiate1(x_1, x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_12 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_mkLetFun(x_5, x_4, x_13, x_6, x_7, x_8, x_9, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_dec(x_4);
lean_inc(x_1);
x_10 = l_Lean_Expr_letFun_x3f(x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Tactic_FunInd_foldCalls___lambda__3(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_20 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_17, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_23 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_18, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_foldCalls___lambda__4___boxed), 10, 4);
lean_closure_set(x_26, 0, x_19);
lean_closure_set(x_26, 1, x_2);
lean_closure_set(x_26, 2, x_3);
lean_closure_set(x_26, 3, x_24);
x_27 = 0;
x_28 = 0;
x_29 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_16, x_27, x_21, x_26, x_28, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_23);
if (x_38 == 0)
{
return x_23;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_23, 0);
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_23);
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
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_20);
if (x_42 == 0)
{
return x_20;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_20, 0);
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_20);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Tactic_FunInd_foldCalls(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("foldCalls: cannot reduce application of ", 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" in ", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_10);
x_12 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__1;
lean_inc(x_11);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_11, x_14);
lean_dec(x_11);
lean_inc(x_1);
x_16 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_13, x_15);
x_17 = lean_array_get_size(x_16);
x_18 = lean_nat_dec_lt(x_10, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = l_Lean_Tactic_FunInd_foldCalls___lambda__5(x_1, x_2, x_3, x_19, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_23 = l_Array_anyMUnsafe_any___at_Lean_Tactic_FunInd_foldCalls___spec__1(x_3, x_16, x_21, x_22);
lean_dec(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Tactic_FunInd_foldCalls___lambda__5(x_1, x_2, x_3, x_24, x_5, x_6, x_7, x_8, x_9);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_5, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_5, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_5, 4);
lean_inc(x_30);
x_31 = lean_ctor_get(x_5, 5);
lean_inc(x_31);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_33 = 0;
lean_ctor_set_uint8(x_26, 9, x_33);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 4, x_30);
lean_ctor_set(x_34, 5, x_31);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_35 = lean_whnf(x_1, x_34, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_expr_eqv(x_1, x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_39 = lean_box(0);
x_40 = l_Lean_Tactic_FunInd_foldCalls___lambda__6(x_2, x_3, x_36, x_39, x_5, x_6, x_7, x_8, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_36);
lean_dec(x_3);
lean_dec(x_2);
x_41 = l_Lean_Expr_getAppFn(x_1);
x_42 = l_Lean_MessageData_ofExpr(x_41);
x_43 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__3;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__5;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_indentExpr(x_1);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__7;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_50, x_5, x_6, x_7, x_8, x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_35);
if (x_56 == 0)
{
return x_35;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_35, 0);
x_58 = lean_ctor_get(x_35, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_35);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_60 = lean_ctor_get_uint8(x_26, 0);
x_61 = lean_ctor_get_uint8(x_26, 1);
x_62 = lean_ctor_get_uint8(x_26, 2);
x_63 = lean_ctor_get_uint8(x_26, 3);
x_64 = lean_ctor_get_uint8(x_26, 4);
x_65 = lean_ctor_get_uint8(x_26, 5);
x_66 = lean_ctor_get_uint8(x_26, 6);
x_67 = lean_ctor_get_uint8(x_26, 7);
x_68 = lean_ctor_get_uint8(x_26, 8);
x_69 = lean_ctor_get_uint8(x_26, 10);
x_70 = lean_ctor_get_uint8(x_26, 11);
lean_dec(x_26);
x_71 = 0;
x_72 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_72, 0, x_60);
lean_ctor_set_uint8(x_72, 1, x_61);
lean_ctor_set_uint8(x_72, 2, x_62);
lean_ctor_set_uint8(x_72, 3, x_63);
lean_ctor_set_uint8(x_72, 4, x_64);
lean_ctor_set_uint8(x_72, 5, x_65);
lean_ctor_set_uint8(x_72, 6, x_66);
lean_ctor_set_uint8(x_72, 7, x_67);
lean_ctor_set_uint8(x_72, 8, x_68);
lean_ctor_set_uint8(x_72, 9, x_71);
lean_ctor_set_uint8(x_72, 10, x_69);
lean_ctor_set_uint8(x_72, 11, x_70);
x_73 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_27);
lean_ctor_set(x_73, 2, x_28);
lean_ctor_set(x_73, 3, x_29);
lean_ctor_set(x_73, 4, x_30);
lean_ctor_set(x_73, 5, x_31);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_74 = lean_whnf(x_1, x_73, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_expr_eqv(x_1, x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_1);
x_78 = lean_box(0);
x_79 = l_Lean_Tactic_FunInd_foldCalls___lambda__6(x_2, x_3, x_75, x_78, x_5, x_6, x_7, x_8, x_76);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_75);
lean_dec(x_3);
lean_dec(x_2);
x_80 = l_Lean_Expr_getAppFn(x_1);
x_81 = l_Lean_MessageData_ofExpr(x_80);
x_82 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__3;
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__5;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_indentExpr(x_1);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__7;
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_89, x_5, x_6, x_7, x_8, x_76);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_ctor_get(x_74, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_74, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_97 = x_74;
} else {
 lean_dec_ref(x_74);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_foldCalls___lambda__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("motive not an arrow", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_foldCalls___lambda__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_foldCalls___lambda__8___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_dec(x_3);
if (lean_obj_tag(x_4) == 7)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l_Lean_Expr_hasLooseBVars(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Tactic_FunInd_foldCalls(x_1, x_2, x_10, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Tactic_FunInd_foldCalls___lambda__8___closed__2;
x_14 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_13, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Tactic_FunInd_foldCalls___lambda__8___closed__2;
x_16 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_15, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_foldCalls), 8, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Tactic_FunInd_removeLamda___rarg(x_3, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_foldCalls___lambda__10___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Tactic_FunInd_foldCalls___lambda__10___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_foldCalls___lambda__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_foldCalls___lambda__10___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_11 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_Lean_Tactic_FunInd_foldCalls___lambda__7(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_41 = lean_ctor_get(x_17, 9);
lean_inc(x_41);
x_42 = lean_array_get_size(x_41);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_dec_eq(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_17);
x_45 = lean_box(0);
x_46 = l_Lean_Tactic_FunInd_foldCalls___lambda__7(x_1, x_2, x_3, x_45, x_5, x_6, x_7, x_8, x_16);
return x_46;
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_nat_dec_lt(x_47, x_42);
lean_dec(x_42);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_41);
x_49 = l_Lean_instInhabitedExpr;
x_50 = l___private_Init_Util_0__outOfBounds___rarg(x_49);
x_51 = l_Lean_Expr_isFVarOf(x_50, x_3);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_17);
x_52 = lean_box(0);
x_53 = l_Lean_Tactic_FunInd_foldCalls___lambda__7(x_1, x_2, x_3, x_52, x_5, x_6, x_7, x_8, x_16);
return x_53;
}
else
{
lean_object* x_54; 
lean_dec(x_1);
x_54 = lean_box(0);
x_18 = x_54;
goto block_40;
}
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_array_fget(x_41, x_47);
lean_dec(x_41);
x_56 = l_Lean_Expr_isFVarOf(x_55, x_3);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_17);
x_57 = lean_box(0);
x_58 = l_Lean_Tactic_FunInd_foldCalls___lambda__7(x_1, x_2, x_3, x_57, x_5, x_6, x_7, x_8, x_16);
return x_58;
}
else
{
lean_object* x_59; 
lean_dec(x_1);
x_59 = lean_box(0);
x_18 = x_59;
goto block_40;
}
}
}
block_40:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_18);
x_19 = lean_ctor_get(x_17, 6);
lean_inc(x_19);
x_20 = lean_array_get_size(x_19);
lean_dec(x_19);
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_mk_array(x_20, x_22);
lean_inc(x_3);
lean_inc(x_2);
x_24 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_foldCalls), 8, 2);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_3);
lean_inc(x_2);
x_25 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_foldCalls___lambda__8), 9, 2);
lean_closure_set(x_25, 0, x_2);
lean_closure_set(x_25, 1, x_3);
x_26 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_foldCalls___lambda__9___boxed), 8, 1);
lean_closure_set(x_26, 0, x_2);
x_27 = l_Lean_Tactic_FunInd_foldCalls___lambda__11___closed__1;
x_28 = l_Lean_Meta_MatcherApp_transform(x_17, x_21, x_23, x_24, x_25, x_26, x_27, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = l_Lean_Meta_MatcherApp_toExpr(x_30);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = l_Lean_Meta_MatcherApp_toExpr(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_28);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_11);
if (x_60 == 0)
{
return x_11;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_11, 0);
x_62 = lean_ctor_get(x_11, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_11);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_foldCalls___lambda__12___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__1;
x_2 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__2;
x_3 = lean_unsigned_to_nat(181u);
x_4 = lean_unsigned_to_nat(41u);
x_5 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_10);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_Lean_Tactic_FunInd_foldCalls___lambda__11(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Expr_getAppFn(x_1);
x_17 = l_Lean_Expr_isFVarOf(x_16, x_3);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = l_Lean_Tactic_FunInd_foldCalls___lambda__11(x_1, x_2, x_3, x_18, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__1;
lean_inc(x_11);
x_21 = lean_mk_array(x_11, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_11, x_22);
lean_dec(x_11);
lean_inc(x_1);
x_24 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_21, x_23);
x_25 = lean_array_get_size(x_24);
x_26 = lean_nat_dec_eq(x_25, x_12);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
x_27 = l_Lean_Tactic_FunInd_foldCalls___lambda__12___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_28 = l_panic___at___private_Lean_Meta_WHNF_0__Lean_Meta_cache___spec__1(x_27, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Tactic_FunInd_foldCalls___lambda__11(x_1, x_2, x_3, x_29, x_5, x_6, x_7, x_8, x_30);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
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
lean_dec(x_1);
x_36 = lean_array_fget(x_24, x_10);
lean_dec(x_24);
lean_inc(x_2);
x_37 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_36, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = l_Lean_Expr_app___override(x_2, x_39);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = l_Lean_Expr_app___override(x_2, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_37, 0);
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_37);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_2, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Tactic_FunInd_foldCalls___lambda__12(x_3, x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Tactic_FunInd_foldCalls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Tactic_FunInd_foldCalls___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Tactic_FunInd_foldCalls___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Tactic_FunInd_foldCalls___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Tactic_FunInd_foldCalls___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Tactic_FunInd_foldCalls___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Tactic_FunInd_foldCalls___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Tactic_FunInd_foldCalls___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_foldCalls___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Tactic_FunInd_foldCalls___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_panic___at_Lean_Tactic_FunInd_collectIHs___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Tactic_FunInd_collectIHs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Tactic_FunInd_collectIHs___spec__1___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
x_15 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
lean_inc(x_1);
x_16 = lean_array_push(x_15, x_1);
x_17 = 1;
x_18 = 1;
x_19 = l_Lean_Meta_mkLambdaFVars(x_16, x_12, x_17, x_17, x_18, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_24 = lean_array_uset(x_14, x_3, x_20);
x_3 = x_23;
x_4 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_14);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
x_15 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
lean_inc(x_1);
x_16 = lean_array_push(x_15, x_1);
x_17 = 1;
x_18 = 1;
x_19 = l_Lean_Meta_mkLambdaFVars(x_16, x_12, x_17, x_17, x_18, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_24 = lean_array_uset(x_14, x_3, x_20);
x_3 = x_23;
x_4 = x_24;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_14);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
x_15 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
lean_inc(x_1);
x_16 = lean_array_push(x_15, x_1);
x_17 = 0;
x_18 = 1;
x_19 = 1;
x_20 = l_Lean_Meta_mkLambdaFVars(x_16, x_12, x_17, x_18, x_19, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_14, x_3, x_21);
x_3 = x_24;
x_4 = x_25;
x_9 = x_22;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_14);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Tactic_FunInd_collectIHs___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Expr_isFVarOf(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Tactic_FunInd_collectIHs___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Expr_isFVarOf(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_Tactic_FunInd_collectIHs___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_4, x_13);
lean_dec(x_4);
x_15 = lean_array_get_size(x_3);
x_16 = lean_nat_dec_lt(x_14, x_15);
lean_dec(x_15);
x_17 = lean_nat_dec_lt(x_14, x_2);
if (x_16 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_instInhabitedExpr;
x_19 = l___private_Init_Util_0__outOfBounds___rarg(x_18);
if (x_17 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l___private_Init_Util_0__outOfBounds___rarg(x_18);
x_21 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_Meta_kabstract(x_5, x_20, x_21, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_expr_instantiate1(x_23, x_19);
lean_dec(x_19);
lean_dec(x_23);
x_4 = x_14;
x_5 = x_25;
x_10 = x_24;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_array_fget(x_1, x_14);
x_32 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_33 = l_Lean_Meta_kabstract(x_5, x_31, x_32, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_expr_instantiate1(x_34, x_19);
lean_dec(x_19);
lean_dec(x_34);
x_4 = x_14;
x_5 = x_36;
x_10 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
lean_object* x_42; 
x_42 = lean_array_fget(x_3, x_14);
if (x_17 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = l_Lean_instInhabitedExpr;
x_44 = l___private_Init_Util_0__outOfBounds___rarg(x_43);
x_45 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_Meta_kabstract(x_5, x_44, x_45, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_expr_instantiate1(x_47, x_42);
lean_dec(x_42);
lean_dec(x_47);
x_4 = x_14;
x_5 = x_49;
x_10 = x_48;
goto _start;
}
else
{
uint8_t x_51; 
lean_dec(x_42);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_46);
if (x_51 == 0)
{
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_46, 0);
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_46);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_array_fget(x_1, x_14);
x_56 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_57 = l_Lean_Meta_kabstract(x_5, x_55, x_56, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_expr_instantiate1(x_58, x_42);
lean_dec(x_42);
lean_dec(x_58);
x_4 = x_14;
x_5 = x_60;
x_10 = x_59;
goto _start;
}
else
{
uint8_t x_62; 
lean_dec(x_42);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_57, 0);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_57);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
else
{
lean_object* x_66; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_5);
lean_ctor_set(x_66, 1, x_10);
return x_66;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
x_15 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
lean_inc(x_1);
x_16 = lean_array_push(x_15, x_1);
x_17 = 0;
x_18 = 1;
x_19 = 1;
x_20 = l_Lean_Meta_mkLambdaFVars(x_16, x_12, x_17, x_18, x_19, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_14, x_3, x_21);
x_3 = x_24;
x_4 = x_25;
x_9 = x_22;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_14);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_expr_instantiate1(x_1, x_5);
lean_dec(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_12 = l_Lean_Tactic_FunInd_collectIHs(x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_get_size(x_13);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__2(x_5, x_16, x_17, x_13, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_expr_instantiate1(x_1, x_5);
lean_dec(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_12 = l_Lean_Tactic_FunInd_collectIHs(x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_get_size(x_13);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__3(x_5, x_16, x_17, x_13, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_expr_instantiate1(x_1, x_6);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Lean_Tactic_FunInd_collectIHs(x_2, x_3, x_4, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_14);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__4(x_6, x_17, x_18, x_14, x_7, x_8, x_9, x_10, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Array_append___rarg(x_5, x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = l_Array_append___rarg(x_5, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
return x_13;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_13, 0);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_13);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Tactic.FunInd.collectIHs", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__1;
x_2 = l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__1;
x_3 = lean_unsigned_to_nat(349u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("collectIHs: could not collect recursive calls, unsaturated application of old induction hypothesis", 98);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_dec(x_5);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__4;
x_12 = l_Lean_throwError___at_Lean_Meta_collectForwardDeps___spec__1(x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
case 5:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Tactic_FunInd_collectIHs(x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Tactic_FunInd_collectIHs(x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = l_Array_append___rarg(x_16, x_20);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = l_Array_append___rarg(x_16, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_16);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
case 6:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 2);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
x_38 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_35, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_collectIHs___lambda__1), 10, 4);
lean_closure_set(x_41, 0, x_36);
lean_closure_set(x_41, 1, x_2);
lean_closure_set(x_41, 2, x_3);
lean_closure_set(x_41, 3, x_4);
x_42 = 0;
x_43 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_34, x_37, x_39, x_41, x_42, x_6, x_7, x_8, x_9, x_40);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
return x_43;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_43, 0);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_43);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_38);
if (x_52 == 0)
{
return x_38;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_38, 0);
x_54 = lean_ctor_get(x_38, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_38);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
case 7:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_1, 2);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
x_60 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_57, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_collectIHs___lambda__2), 10, 4);
lean_closure_set(x_63, 0, x_58);
lean_closure_set(x_63, 1, x_2);
lean_closure_set(x_63, 2, x_3);
lean_closure_set(x_63, 3, x_4);
x_64 = 0;
x_65 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_56, x_59, x_61, x_63, x_64, x_6, x_7, x_8, x_9, x_62);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
return x_65;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_65);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_65);
if (x_70 == 0)
{
return x_65;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_65, 0);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_65);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_60);
if (x_74 == 0)
{
return x_60;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_60, 0);
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_60);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
case 8:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_1, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_1, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_1, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_1, 3);
lean_inc(x_81);
lean_dec(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_80);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_82 = l_Lean_Tactic_FunInd_collectIHs(x_2, x_3, x_4, x_80, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
x_85 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_80, x_6, x_7, x_8, x_9, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_collectIHs___lambda__3___boxed), 11, 5);
lean_closure_set(x_88, 0, x_81);
lean_closure_set(x_88, 1, x_2);
lean_closure_set(x_88, 2, x_3);
lean_closure_set(x_88, 3, x_4);
lean_closure_set(x_88, 4, x_83);
x_89 = 0;
x_90 = l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1___rarg(x_78, x_79, x_86, x_88, x_89, x_6, x_7, x_8, x_9, x_87);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
return x_90;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_90);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_90);
if (x_95 == 0)
{
return x_90;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_90, 0);
x_97 = lean_ctor_get(x_90, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_90);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_85);
if (x_99 == 0)
{
return x_85;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_85, 0);
x_101 = lean_ctor_get(x_85, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_85);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_82);
if (x_103 == 0)
{
return x_82;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_82, 0);
x_105 = lean_ctor_get(x_82, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_82);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
case 10:
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_1, 1);
lean_inc(x_107);
lean_dec(x_1);
x_108 = l_Lean_Tactic_FunInd_collectIHs(x_2, x_3, x_4, x_107, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
return x_108;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_108);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
else
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_108);
if (x_113 == 0)
{
return x_108;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_108, 0);
x_115 = lean_ctor_get(x_108, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_108);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
case 11:
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_1, 2);
lean_inc(x_117);
lean_dec(x_1);
x_118 = l_Lean_Tactic_FunInd_collectIHs(x_2, x_3, x_4, x_117, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
return x_118;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_118);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
else
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_118);
if (x_123 == 0)
{
return x_118;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_118, 0);
x_125 = lean_ctor_get(x_118, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_118);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
default: 
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_127 = l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__2;
x_128 = l_panic___at_Lean_Tactic_FunInd_collectIHs___spec__1(x_127, x_6, x_7, x_8, x_9, x_10);
return x_128;
}
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_collectIHs___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("collectIHs: could not collect recursive calls from call ", 56);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_collectIHs___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_collectIHs___lambda__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_11);
x_13 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
lean_inc(x_1);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = lean_array_get_size(x_17);
x_19 = lean_nat_dec_lt(x_11, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = l_Lean_Tactic_FunInd_collectIHs___lambda__4(x_1, x_2, x_3, x_4, x_20, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_24 = l_Array_anyMUnsafe_any___at_Lean_Tactic_FunInd_collectIHs___spec__5(x_3, x_17, x_22, x_23);
lean_dec(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Lean_Tactic_FunInd_collectIHs___lambda__4(x_1, x_2, x_3, x_4, x_25, x_6, x_7, x_8, x_9, x_10);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = l_Lean_indentExpr(x_1);
x_28 = l_Lean_Tactic_FunInd_collectIHs___lambda__5___closed__2;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_31, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Tactic_FunInd_collectIHs(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_collectIHs___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("collectIHs: cannot reduce application of ", 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_collectIHs___lambda__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_collectIHs___lambda__7___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_11);
x_13 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
lean_inc(x_1);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = lean_array_get_size(x_17);
x_19 = lean_nat_dec_lt(x_11, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = l_Lean_Tactic_FunInd_collectIHs___lambda__5(x_1, x_2, x_3, x_4, x_20, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_24 = l_Array_anyMUnsafe_any___at_Lean_Tactic_FunInd_collectIHs___spec__6(x_3, x_17, x_22, x_23);
lean_dec(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Lean_Tactic_FunInd_collectIHs___lambda__5(x_1, x_2, x_3, x_4, x_25, x_6, x_7, x_8, x_9, x_10);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_6, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_6, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_6, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_6, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_6, 5);
lean_inc(x_32);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_34 = 0;
lean_ctor_set_uint8(x_27, 9, x_34);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_31);
lean_ctor_set(x_35, 5, x_32);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_36 = lean_whnf(x_1, x_35, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_expr_eqv(x_1, x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_1);
x_40 = lean_box(0);
x_41 = l_Lean_Tactic_FunInd_collectIHs___lambda__6(x_2, x_3, x_4, x_37, x_40, x_6, x_7, x_8, x_9, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_37);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = l_Lean_Expr_getAppFn(x_1);
x_43 = l_Lean_MessageData_ofExpr(x_42);
x_44 = l_Lean_Tactic_FunInd_collectIHs___lambda__7___closed__2;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__5;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_indentExpr(x_1);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__7;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_51, x_6, x_7, x_8, x_9, x_38);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
return x_52;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_36);
if (x_57 == 0)
{
return x_36;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_36, 0);
x_59 = lean_ctor_get(x_36, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_36);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_61 = lean_ctor_get_uint8(x_27, 0);
x_62 = lean_ctor_get_uint8(x_27, 1);
x_63 = lean_ctor_get_uint8(x_27, 2);
x_64 = lean_ctor_get_uint8(x_27, 3);
x_65 = lean_ctor_get_uint8(x_27, 4);
x_66 = lean_ctor_get_uint8(x_27, 5);
x_67 = lean_ctor_get_uint8(x_27, 6);
x_68 = lean_ctor_get_uint8(x_27, 7);
x_69 = lean_ctor_get_uint8(x_27, 8);
x_70 = lean_ctor_get_uint8(x_27, 10);
x_71 = lean_ctor_get_uint8(x_27, 11);
lean_dec(x_27);
x_72 = 0;
x_73 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_73, 0, x_61);
lean_ctor_set_uint8(x_73, 1, x_62);
lean_ctor_set_uint8(x_73, 2, x_63);
lean_ctor_set_uint8(x_73, 3, x_64);
lean_ctor_set_uint8(x_73, 4, x_65);
lean_ctor_set_uint8(x_73, 5, x_66);
lean_ctor_set_uint8(x_73, 6, x_67);
lean_ctor_set_uint8(x_73, 7, x_68);
lean_ctor_set_uint8(x_73, 8, x_69);
lean_ctor_set_uint8(x_73, 9, x_72);
lean_ctor_set_uint8(x_73, 10, x_70);
lean_ctor_set_uint8(x_73, 11, x_71);
x_74 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_28);
lean_ctor_set(x_74, 2, x_29);
lean_ctor_set(x_74, 3, x_30);
lean_ctor_set(x_74, 4, x_31);
lean_ctor_set(x_74, 5, x_32);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_75 = lean_whnf(x_1, x_74, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_expr_eqv(x_1, x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_1);
x_79 = lean_box(0);
x_80 = l_Lean_Tactic_FunInd_collectIHs___lambda__6(x_2, x_3, x_4, x_76, x_79, x_6, x_7, x_8, x_9, x_77);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_76);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_81 = l_Lean_Expr_getAppFn(x_1);
x_82 = l_Lean_MessageData_ofExpr(x_81);
x_83 = l_Lean_Tactic_FunInd_collectIHs___lambda__7___closed__2;
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__5;
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_indentExpr(x_1);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__7;
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_90, x_6, x_7, x_8, x_9, x_77);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = lean_ctor_get(x_75, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_75, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_98 = x_75;
} else {
 lean_dec_ref(x_75);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_collectIHs___lambda__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("True", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_collectIHs___lambda__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Tactic_FunInd_collectIHs___lambda__8___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_collectIHs___lambda__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Tactic_FunInd_collectIHs___lambda__8___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_6);
x_11 = l_Lean_FVarId_getType(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_14 = l_Nat_foldRevM_loop___at_Lean_Tactic_FunInd_collectIHs___spec__7(x_2, x_3, x_4, x_3, x_12, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Tactic_FunInd_collectIHs___lambda__8___closed__3;
x_18 = l_Lean_mkArrow(x_15, x_17, x_8, x_9, x_16);
lean_dec(x_9);
lean_dec(x_8);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_collectIHs___lambda__9___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__1;
x_2 = l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__1;
x_3 = lean_unsigned_to_nat(296u);
x_4 = lean_unsigned_to_nat(40u);
x_5 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_get_size(x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Tactic_FunInd_collectIHs___lambda__9___closed__1;
x_15 = l_panic___at_Lean_Meta_whnfCore_go___spec__1(x_14, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fget(x_4, x_16);
lean_inc(x_17);
x_18 = l_Lean_Expr_fvarId_x21(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Tactic_FunInd_collectIHs(x_1, x_2, x_18, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_Meta_mkAndIntroN(x_20, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
x_26 = lean_array_push(x_25, x_17);
x_27 = 0;
x_28 = 1;
x_29 = 1;
x_30 = l_Lean_Meta_mkLambdaFVars(x_26, x_23, x_27, x_28, x_29, x_6, x_7, x_8, x_9, x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
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
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_collectIHs___lambda__10___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_collectIHs___lambda__9___boxed), 10, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = l_Lean_Tactic_FunInd_collectIHs___lambda__10___closed__1;
x_12 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__5___rarg(x_2, x_11, x_10, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_collectIHs___lambda__10), 9, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lean_Tactic_FunInd_removeLamda___rarg(x_3, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Expr_fvar___override(x_1);
x_9 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
x_10 = lean_array_push(x_9, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_12 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1(x_1, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_Lean_Tactic_FunInd_collectIHs___lambda__7(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_53 = lean_ctor_get(x_18, 9);
lean_inc(x_53);
x_54 = lean_array_get_size(x_53);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_dec_eq(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_18);
x_57 = lean_box(0);
x_58 = l_Lean_Tactic_FunInd_collectIHs___lambda__7(x_1, x_2, x_3, x_4, x_57, x_6, x_7, x_8, x_9, x_17);
return x_58;
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_nat_dec_lt(x_59, x_54);
lean_dec(x_54);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_53);
x_61 = l_Lean_instInhabitedExpr;
x_62 = l___private_Init_Util_0__outOfBounds___rarg(x_61);
x_63 = l_Lean_Expr_isFVarOf(x_62, x_3);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_18);
x_64 = lean_box(0);
x_65 = l_Lean_Tactic_FunInd_collectIHs___lambda__7(x_1, x_2, x_3, x_4, x_64, x_6, x_7, x_8, x_9, x_17);
return x_65;
}
else
{
lean_object* x_66; 
lean_dec(x_1);
x_66 = lean_box(0);
x_19 = x_66;
goto block_52;
}
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_array_fget(x_53, x_59);
lean_dec(x_53);
x_68 = l_Lean_Expr_isFVarOf(x_67, x_3);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_18);
x_69 = lean_box(0);
x_70 = l_Lean_Tactic_FunInd_collectIHs___lambda__7(x_1, x_2, x_3, x_4, x_69, x_6, x_7, x_8, x_9, x_17);
return x_70;
}
else
{
lean_object* x_71; 
lean_dec(x_1);
x_71 = lean_box(0);
x_19 = x_71;
goto block_52;
}
}
}
block_52:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
x_20 = lean_ctor_get(x_18, 6);
lean_inc(x_20);
x_21 = lean_array_get_size(x_20);
x_22 = 0;
x_23 = lean_box(x_22);
lean_inc(x_21);
x_24 = lean_mk_array(x_21, x_23);
lean_inc(x_2);
x_25 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_foldCalls), 8, 2);
lean_closure_set(x_25, 0, x_2);
lean_closure_set(x_25, 1, x_3);
lean_inc(x_4);
x_26 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_collectIHs___lambda__8___boxed), 10, 3);
lean_closure_set(x_26, 0, x_4);
lean_closure_set(x_26, 1, x_20);
lean_closure_set(x_26, 2, x_21);
x_27 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_collectIHs___lambda__11), 8, 1);
lean_closure_set(x_27, 0, x_2);
x_28 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_collectIHs___lambda__12___boxed), 7, 1);
lean_closure_set(x_28, 0, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = l_Lean_Meta_MatcherApp_transform(x_18, x_22, x_24, x_25, x_26, x_27, x_28, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Meta_MatcherApp_inferMatchType(x_30, x_6, x_7, x_8, x_9, x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = l_Lean_Meta_MatcherApp_toExpr(x_34);
x_36 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
x_37 = lean_array_push(x_36, x_35);
lean_ctor_set(x_32, 0, x_37);
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = l_Lean_Meta_MatcherApp_toExpr(x_38);
x_41 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
x_42 = lean_array_push(x_41, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_32);
if (x_44 == 0)
{
return x_32;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_32, 0);
x_46 = lean_ctor_get(x_32, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_32);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_48 = !lean_is_exclusive(x_29);
if (x_48 == 0)
{
return x_29;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_29, 0);
x_50 = lean_ctor_get(x_29, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_29);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_12);
if (x_72 == 0)
{
return x_12;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_12, 0);
x_74 = lean_ctor_get(x_12, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_12);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_expr_instantiate1(x_1, x_6);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Lean_Tactic_FunInd_collectIHs(x_2, x_3, x_4, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_14);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__8(x_6, x_17, x_18, x_14, x_7, x_8, x_9, x_10, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Array_append___rarg(x_5, x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = l_Array_append___rarg(x_5, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
return x_13;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_13, 0);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_13);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_dec(x_5);
lean_inc(x_1);
x_11 = l_Lean_Expr_letFun_x3f(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lean_Tactic_FunInd_collectIHs___lambda__13(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_19);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Lean_Tactic_FunInd_collectIHs(x_2, x_3, x_4, x_19, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
x_24 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_19, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_collectIHs___lambda__14___boxed), 11, 5);
lean_closure_set(x_27, 0, x_20);
lean_closure_set(x_27, 1, x_2);
lean_closure_set(x_27, 2, x_3);
lean_closure_set(x_27, 3, x_4);
lean_closure_set(x_27, 4, x_22);
x_28 = 0;
x_29 = l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1___rarg(x_17, x_18, x_25, x_27, x_28, x_6, x_7, x_8, x_9, x_26);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
return x_24;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = lean_ctor_get(x_24, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_24);
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
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
return x_21;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_21, 0);
x_44 = lean_ctor_get(x_21, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_21);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_collectIHs___lambda__16___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__1;
x_2 = l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__1;
x_3 = lean_unsigned_to_nat(259u);
x_4 = lean_unsigned_to_nat(41u);
x_5 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_Lean_Tactic_FunInd_collectIHs___lambda__15(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Expr_getAppFn(x_1);
x_18 = l_Lean_Expr_isFVarOf(x_17, x_3);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = l_Lean_Tactic_FunInd_collectIHs___lambda__15(x_1, x_2, x_3, x_4, x_19, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__1;
lean_inc(x_12);
x_22 = lean_mk_array(x_12, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_12, x_23);
lean_dec(x_12);
lean_inc(x_1);
x_25 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_22, x_24);
x_26 = lean_array_get_size(x_25);
x_27 = lean_nat_dec_eq(x_26, x_13);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
x_28 = l_Lean_Tactic_FunInd_collectIHs___lambda__16___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = l_panic___at___private_Lean_Meta_WHNF_0__Lean_Meta_cache___spec__1(x_28, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Tactic_FunInd_collectIHs___lambda__15(x_1, x_2, x_3, x_4, x_30, x_6, x_7, x_8, x_9, x_31);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_1);
x_37 = lean_array_fget(x_25, x_11);
x_38 = lean_array_fget(x_25, x_23);
lean_dec(x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_37);
lean_inc(x_3);
lean_inc(x_2);
x_39 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_37, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
x_42 = l_Lean_Tactic_FunInd_foldCalls(x_2, x_3, x_38, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_4);
x_45 = l_Lean_Tactic_FunInd_collectIHs(x_2, x_3, x_4, x_37, x_6, x_7, x_8, x_9, x_44);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = l_Lean_Expr_fvar___override(x_4);
x_49 = l_Lean_mkAppB(x_48, x_40, x_43);
x_50 = lean_array_push(x_47, x_49);
lean_ctor_set(x_45, 0, x_50);
return x_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_45, 0);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_45);
x_53 = l_Lean_Expr_fvar___override(x_4);
x_54 = l_Lean_mkAppB(x_53, x_40, x_43);
x_55 = lean_array_push(x_51, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_45);
if (x_57 == 0)
{
return x_45;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_45, 0);
x_59 = lean_ctor_get(x_45, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_45);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_42);
if (x_61 == 0)
{
return x_42;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_42, 0);
x_63 = lean_ctor_get(x_42, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_42);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_39);
if (x_65 == 0)
{
return x_39;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_39, 0);
x_67 = lean_ctor_get(x_39, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_39);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_2, x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Tactic_FunInd_foldCalls___lambda__10___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Tactic_FunInd_collectIHs___lambda__16(x_4, x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__3(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__4(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Tactic_FunInd_collectIHs___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Tactic_FunInd_collectIHs___spec__5(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Tactic_FunInd_collectIHs___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Tactic_FunInd_collectIHs___spec__6(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_Tactic_FunInd_collectIHs___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldRevM_loop___at_Lean_Tactic_FunInd_collectIHs___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_collectIHs___spec__8(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Tactic_FunInd_collectIHs___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Tactic_FunInd_collectIHs___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Tactic_FunInd_collectIHs___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Tactic_FunInd_collectIHs___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Tactic_FunInd_collectIHs___lambda__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_collectIHs___lambda__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Tactic_FunInd_collectIHs___lambda__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deduplicateIHs___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_1, x_3);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_12);
x_16 = lean_infer_type(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Array_contains___at_Lean_Elab_Term_collectUnassignedMVars_go___spec__1(x_14, x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_20 = lean_array_push(x_15, x_12);
x_21 = lean_array_push(x_14, x_17);
lean_ctor_set(x_4, 1, x_20);
lean_ctor_set(x_4, 0, x_21);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
x_9 = x_18;
goto _start;
}
else
{
size_t x_25; size_t x_26; 
lean_dec(x_17);
lean_dec(x_12);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_3 = x_26;
x_9 = x_18;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_12);
x_34 = lean_infer_type(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Array_contains___at_Lean_Elab_Term_collectUnassignedMVars_go___spec__1(x_32, x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; 
x_38 = lean_array_push(x_33, x_12);
x_39 = lean_array_push(x_32, x_35);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = 1;
x_42 = lean_usize_add(x_3, x_41);
x_3 = x_42;
x_4 = x_40;
x_9 = x_36;
goto _start;
}
else
{
lean_object* x_44; size_t x_45; size_t x_46; 
lean_dec(x_35);
lean_dec(x_12);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_32);
lean_ctor_set(x_44, 1, x_33);
x_45 = 1;
x_46 = lean_usize_add(x_3, x_45);
x_3 = x_46;
x_4 = x_44;
x_9 = x_36;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_48 = lean_ctor_get(x_34, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_50 = x_34;
} else {
 lean_dec_ref(x_34);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_deduplicateIHs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_foldCalls___lambda__10___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_deduplicateIHs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = l_Lean_Tactic_FunInd_deduplicateIHs___closed__1;
x_11 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deduplicateIHs___spec__1(x_1, x_8, x_9, x_10, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deduplicateIHs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deduplicateIHs___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_deduplicateIHs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Tactic_FunInd_deduplicateIHs(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_assertIHs___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ih", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_assertIHs___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_1, x_3);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 2);
lean_inc(x_18);
x_19 = lean_nat_dec_lt(x_16, x_17);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_14, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_14, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = lean_nat_add(x_16, x_18);
lean_ctor_set(x_14, 0, x_25);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_12);
x_26 = lean_infer_type(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_16, x_29);
lean_dec(x_16);
x_31 = l_Nat_repr(x_30);
x_32 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_assertIHs___spec__1___closed__1;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__3;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_box(0);
x_37 = l_Lean_Name_str___override(x_36, x_35);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_38 = l_Lean_MVarId_assert(x_15, x_37, x_27, x_12, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_ctor_set(x_4, 1, x_39);
x_41 = 1;
x_42 = lean_usize_add(x_3, x_41);
x_3 = x_42;
x_9 = x_40;
goto _start;
}
else
{
uint8_t x_44; 
lean_dec(x_14);
lean_free_object(x_4);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
return x_38;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_38, 0);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_38);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_16);
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_48 = !lean_is_exclusive(x_26);
if (x_48 == 0)
{
return x_26;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_26, 0);
x_50 = lean_ctor_get(x_26, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_26);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_14);
x_52 = lean_nat_add(x_16, x_18);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_17);
lean_ctor_set(x_53, 2, x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_12);
x_54 = lean_infer_type(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_16, x_57);
lean_dec(x_16);
x_59 = l_Nat_repr(x_58);
x_60 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_assertIHs___spec__1___closed__1;
x_61 = lean_string_append(x_60, x_59);
lean_dec(x_59);
x_62 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__3;
x_63 = lean_string_append(x_61, x_62);
x_64 = lean_box(0);
x_65 = l_Lean_Name_str___override(x_64, x_63);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_66 = l_Lean_MVarId_assert(x_15, x_65, x_55, x_12, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; size_t x_69; size_t x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_ctor_set(x_4, 1, x_67);
lean_ctor_set(x_4, 0, x_53);
x_69 = 1;
x_70 = lean_usize_add(x_3, x_69);
x_3 = x_70;
x_9 = x_68;
goto _start;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_53);
lean_free_object(x_4);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_72 = lean_ctor_get(x_66, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_74 = x_66;
} else {
 lean_dec_ref(x_66);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_53);
lean_dec(x_16);
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_76 = lean_ctor_get(x_54, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_54, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_78 = x_54;
} else {
 lean_dec_ref(x_54);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_80 = lean_ctor_get(x_4, 0);
x_81 = lean_ctor_get(x_4, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_4);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_80, 2);
lean_inc(x_84);
x_85 = lean_nat_dec_lt(x_82, x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_81);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_9);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 x_88 = x_80;
} else {
 lean_dec_ref(x_80);
 x_88 = lean_box(0);
}
x_89 = lean_nat_add(x_82, x_84);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 3, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_83);
lean_ctor_set(x_90, 2, x_84);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_12);
x_91 = lean_infer_type(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_add(x_82, x_94);
lean_dec(x_82);
x_96 = l_Nat_repr(x_95);
x_97 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_assertIHs___spec__1___closed__1;
x_98 = lean_string_append(x_97, x_96);
lean_dec(x_96);
x_99 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__3;
x_100 = lean_string_append(x_98, x_99);
x_101 = lean_box(0);
x_102 = l_Lean_Name_str___override(x_101, x_100);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_103 = l_Lean_MVarId_assert(x_81, x_102, x_92, x_12, x_5, x_6, x_7, x_8, x_93);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; size_t x_107; size_t x_108; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_90);
lean_ctor_set(x_106, 1, x_104);
x_107 = 1;
x_108 = lean_usize_add(x_3, x_107);
x_3 = x_108;
x_4 = x_106;
x_9 = x_105;
goto _start;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_90);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_110 = lean_ctor_get(x_103, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_103, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_112 = x_103;
} else {
 lean_dec_ref(x_103);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_90);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_114 = lean_ctor_get(x_91, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_91, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_116 = x_91;
} else {
 lean_dec_ref(x_91);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_assertIHs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_Array_reverse___rarg(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_2);
x_14 = lean_array_get_size(x_12);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_assertIHs___spec__1(x_12, x_15, x_16, x_13, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_12);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_assertIHs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_assertIHs___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_substVarAfter___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_uget(x_4, x_6);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_7, 1);
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_17);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Lean_PersistentArray_forInAux___at_Lean_Tactic_FunInd_substVarAfter___spec__2(x_1, x_2, x_15, x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_7, 0, x_23);
lean_ctor_set(x_19, 0, x_7);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_7, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
lean_dec(x_17);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_28);
lean_ctor_set(x_7, 0, x_3);
x_29 = 1;
x_30 = lean_usize_add(x_6, x_29);
x_6 = x_30;
x_12 = x_27;
goto _start;
}
}
else
{
uint8_t x_32; 
lean_free_object(x_7);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
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
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_36);
lean_inc(x_2);
lean_inc(x_1);
x_37 = l_Lean_PersistentArray_forInAux___at_Lean_Tactic_FunInd_substVarAfter___spec__2(x_1, x_2, x_15, x_36, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_ctor_set(x_42, 1, x_36);
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
lean_dec(x_36);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec(x_38);
lean_inc(x_3);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_3);
lean_ctor_set(x_46, 1, x_45);
x_47 = 1;
x_48 = lean_usize_add(x_6, x_47);
x_6 = x_48;
x_7 = x_46;
x_12 = x_44;
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_36);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_substVarAfter___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_3, x_5);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_16 = x_6;
} else {
 lean_dec_ref(x_6);
 x_16 = lean_box(0);
}
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_15);
x_17 = x_25;
x_18 = x_11;
goto block_24;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
lean_dec(x_14);
x_27 = l_Lean_LocalDecl_index(x_26);
x_28 = lean_nat_dec_lt(x_1, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_15);
x_17 = x_29;
x_18 = x_11;
goto block_24;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_LocalDecl_fvarId(x_26);
lean_dec(x_26);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Meta_trySubstVar(x_15, x_30, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_32);
x_17 = x_34;
x_18 = x_33;
goto block_24;
}
else
{
uint8_t x_35; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
block_24:
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_2);
if (lean_is_scalar(x_16)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_16;
}
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
x_21 = 1;
x_22 = lean_usize_add(x_5, x_21);
x_5 = x_22;
x_6 = x_20;
x_11 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Tactic_FunInd_substVarAfter___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Tactic_FunInd_substVarAfter___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
x_13 = lean_array_get_size(x_10);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_substVarAfter___spec__3(x_1, x_2, x_11, x_10, x_14, x_15, x_12, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l_Lean_PersistentArray_forInAux___at_Lean_Tactic_FunInd_substVarAfter___spec__2___lambda__1(x_20, x_21, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
lean_dec(x_2);
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
lean_dec(x_3);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_4);
x_36 = lean_array_get_size(x_33);
x_37 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_38 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_39 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_substVarAfter___spec__4(x_1, x_34, x_33, x_37, x_38, x_35, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_33);
lean_dec(x_1);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_box(0);
x_45 = l_Lean_PersistentArray_forInAux___at_Lean_Tactic_FunInd_substVarAfter___spec__2___lambda__1(x_43, x_44, x_5, x_6, x_7, x_8, x_42);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_40);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_39, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_41, 0);
lean_inc(x_48);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_48);
return x_39;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_39, 1);
lean_inc(x_49);
lean_dec(x_39);
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
lean_dec(x_41);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_39);
if (x_52 == 0)
{
return x_39;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_39, 0);
x_54 = lean_ctor_get(x_39, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_39);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_substVarAfter___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_3, x_5);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_16 = x_6;
} else {
 lean_dec_ref(x_6);
 x_16 = lean_box(0);
}
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_15);
x_17 = x_25;
x_18 = x_11;
goto block_24;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
lean_dec(x_14);
x_27 = l_Lean_LocalDecl_index(x_26);
x_28 = lean_nat_dec_lt(x_1, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_15);
x_17 = x_29;
x_18 = x_11;
goto block_24;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_LocalDecl_fvarId(x_26);
lean_dec(x_26);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Meta_trySubstVar(x_15, x_30, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_32);
x_17 = x_34;
x_18 = x_33;
goto block_24;
}
else
{
uint8_t x_35; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
block_24:
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_2);
if (lean_is_scalar(x_16)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_16;
}
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
x_21 = 1;
x_22 = lean_usize_add(x_5, x_21);
x_5 = x_22;
x_6 = x_20;
x_11 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Tactic_FunInd_substVarAfter___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Tactic_FunInd_substVarAfter___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_PersistentArray_forInAux___at_Lean_Tactic_FunInd_substVarAfter___spec__2(x_1, x_3, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_array_get_size(x_20);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_substVarAfter___spec__5(x_1, x_21, x_20, x_24, x_25, x_22, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_20);
lean_dec(x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_27);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_26, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_37);
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_dec(x_26);
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_26);
if (x_41 == 0)
{
return x_26;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_26, 0);
x_43 = lean_ctor_get(x_26, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_26);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_10);
if (x_45 == 0)
{
return x_10;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_10, 0);
x_47 = lean_ctor_get(x_10, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_10);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_substVarAfter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_3);
x_8 = l_Lean_FVarId_getDecl(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_LocalDecl_index(x_9);
lean_dec(x_9);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_PersistentArray_forIn___at_Lean_Tactic_FunInd_substVarAfter___spec__1(x_11, x_13, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
return x_8;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_substVarAfter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_substVarAfter___lambda__1), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_substVarAfter___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_substVarAfter___spec__3(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_substVarAfter___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_substVarAfter___spec__4(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_Tactic_FunInd_substVarAfter___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forInAux___at_Lean_Tactic_FunInd_substVarAfter___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_substVarAfter___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_substVarAfter___spec__5(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_Tactic_FunInd_substVarAfter___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forIn___at_Lean_Tactic_FunInd_substVarAfter___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_buildInductionCase___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_1, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_MVarId_clear(x_4, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_4 = x_14;
x_9 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_buildInductionCase___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hyp", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_buildInductionCase___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Tactic_FunInd_buildInductionCase___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionCase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_14 = l_Lean_Tactic_FunInd_collectIHs(x_1, x_2, x_3, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Array_append___rarg(x_7, x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_18 = l_Lean_Tactic_FunInd_deduplicateIHs(x_17, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Tactic_FunInd_buildInductionCase___closed__2;
lean_inc(x_9);
x_22 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_6, x_21, x_9, x_10, x_11, x_12, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_23);
x_25 = l_Lean_Expr_mvarId_x21(x_23);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_26 = l_Lean_Tactic_FunInd_assertIHs(x_19, x_25, x_9, x_10, x_11, x_12, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_array_get_size(x_4);
x_30 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_31 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_32 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_buildInductionCase___spec__1(x_4, x_30, x_31, x_27, x_9, x_10, x_11, x_12, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = 1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_36 = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(x_33, x_5, x_35, x_9, x_10, x_11, x_12, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_23, x_9, x_10, x_11, x_12, x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_47 = !lean_is_exclusive(x_32);
if (x_47 == 0)
{
return x_32;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_32, 0);
x_49 = lean_ctor_get(x_32, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_32);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_51 = !lean_is_exclusive(x_26);
if (x_51 == 0)
{
return x_26;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_26, 0);
x_53 = lean_ctor_get(x_26, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_26);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_55 = !lean_is_exclusive(x_18);
if (x_55 == 0)
{
return x_18;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_18, 0);
x_57 = lean_ctor_get(x_18, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_18);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_59 = !lean_is_exclusive(x_14);
if (x_59 == 0)
{
return x_14;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_14, 0);
x_61 = lean_ctor_get(x_14, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_14);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_buildInductionCase___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_buildInductionCase___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionCase___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Tactic_FunInd_buildInductionCase(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Tactic_FunInd_mkLambdaFVarsMasked___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_pop(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Tactic_FunInd_mkLambdaFVarsMasked___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Tactic_FunInd_mkLambdaFVarsMasked___spec__1___lambda__1___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Tactic_FunInd_mkLambdaFVarsMasked___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
x_13 = l_Array_isEmpty___rarg(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_free_object(x_8);
lean_free_object(x_1);
x_14 = l_Lean_instInhabitedExpr;
x_15 = l_Array_back___rarg(x_14, x_12);
x_16 = l_Lean_Loop_forIn_loop___at_Lean_Tactic_FunInd_mkLambdaFVarsMasked___spec__1___closed__1;
x_17 = l_Lean_Expr_isFVar(x_15);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_array_push(x_11, x_19);
x_21 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = lean_apply_9(x_16, x_10, x_20, x_12, x_21, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
x_1 = x_31;
x_6 = x_30;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
return x_22;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; uint8_t x_38; 
lean_inc(x_15);
x_37 = l_Lean_Expr_fvarId_x21(x_15);
x_38 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_37, x_10);
lean_dec(x_37);
if (x_38 == 0)
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_15);
x_39 = 0;
x_40 = lean_box(x_39);
x_41 = lean_array_push(x_11, x_40);
x_42 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_43 = lean_apply_9(x_16, x_10, x_41, x_12, x_42, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
lean_dec(x_44);
lean_ctor_set(x_43, 0, x_47);
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_dec(x_43);
x_49 = lean_ctor_get(x_44, 0);
lean_inc(x_49);
lean_dec(x_44);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
lean_dec(x_43);
x_52 = lean_ctor_get(x_44, 0);
lean_inc(x_52);
lean_dec(x_44);
x_1 = x_52;
x_6 = x_51;
goto _start;
}
}
else
{
uint8_t x_54; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_43);
if (x_54 == 0)
{
return x_43;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_43, 0);
x_56 = lean_ctor_get(x_43, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_43);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; 
x_58 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
x_59 = lean_array_push(x_58, x_15);
x_60 = 0;
x_61 = 1;
x_62 = 1;
x_63 = l_Lean_Meta_mkLambdaFVars(x_59, x_10, x_60, x_61, x_62, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_box(x_61);
x_67 = lean_array_push(x_11, x_66);
x_68 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_69 = lean_apply_9(x_16, x_64, x_67, x_12, x_68, x_2, x_3, x_4, x_5, x_65);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_69, 0);
lean_dec(x_72);
x_73 = lean_ctor_get(x_70, 0);
lean_inc(x_73);
lean_dec(x_70);
lean_ctor_set(x_69, 0, x_73);
return x_69;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_dec(x_69);
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
lean_dec(x_70);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
lean_dec(x_69);
x_78 = lean_ctor_get(x_70, 0);
lean_inc(x_78);
lean_dec(x_70);
x_1 = x_78;
x_6 = x_77;
goto _start;
}
}
else
{
uint8_t x_80; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_69);
if (x_80 == 0)
{
return x_69;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_69, 0);
x_82 = lean_ctor_get(x_69, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_69);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_63);
if (x_84 == 0)
{
return x_63;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_63, 0);
x_86 = lean_ctor_get(x_63, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_63);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
}
else
{
lean_object* x_88; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_6);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_1, 0);
x_90 = lean_ctor_get(x_8, 0);
x_91 = lean_ctor_get(x_8, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_8);
x_92 = l_Array_isEmpty___rarg(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
lean_free_object(x_1);
x_93 = l_Lean_instInhabitedExpr;
x_94 = l_Array_back___rarg(x_93, x_91);
x_95 = l_Lean_Loop_forIn_loop___at_Lean_Tactic_FunInd_mkLambdaFVarsMasked___spec__1___closed__1;
x_96 = l_Lean_Expr_isFVar(x_94);
if (x_96 == 0)
{
uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_94);
x_97 = 0;
x_98 = lean_box(x_97);
x_99 = lean_array_push(x_90, x_98);
x_100 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_101 = lean_apply_9(x_95, x_89, x_99, x_91, x_100, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_102, 0);
lean_inc(x_105);
lean_dec(x_102);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
lean_dec(x_101);
x_108 = lean_ctor_get(x_102, 0);
lean_inc(x_108);
lean_dec(x_102);
x_1 = x_108;
x_6 = x_107;
goto _start;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = lean_ctor_get(x_101, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_101, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_112 = x_101;
} else {
 lean_dec_ref(x_101);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; uint8_t x_115; 
lean_inc(x_94);
x_114 = l_Lean_Expr_fvarId_x21(x_94);
x_115 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_114, x_89);
lean_dec(x_114);
if (x_115 == 0)
{
uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_94);
x_116 = 0;
x_117 = lean_box(x_116);
x_118 = lean_array_push(x_90, x_117);
x_119 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_120 = lean_apply_9(x_95, x_89, x_118, x_91, x_119, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_121, 0);
lean_inc(x_124);
lean_dec(x_121);
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_122);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_120, 1);
lean_inc(x_126);
lean_dec(x_120);
x_127 = lean_ctor_get(x_121, 0);
lean_inc(x_127);
lean_dec(x_121);
x_1 = x_127;
x_6 = x_126;
goto _start;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_129 = lean_ctor_get(x_120, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_120, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_131 = x_120;
} else {
 lean_dec_ref(x_120);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; lean_object* x_138; 
x_133 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
x_134 = lean_array_push(x_133, x_94);
x_135 = 0;
x_136 = 1;
x_137 = 1;
x_138 = l_Lean_Meta_mkLambdaFVars(x_134, x_89, x_135, x_136, x_137, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_box(x_136);
x_142 = lean_array_push(x_90, x_141);
x_143 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_144 = lean_apply_9(x_95, x_139, x_142, x_91, x_143, x_2, x_3, x_4, x_5, x_140);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_145, 0);
lean_inc(x_148);
lean_dec(x_145);
if (lean_is_scalar(x_147)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_147;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_144, 1);
lean_inc(x_150);
lean_dec(x_144);
x_151 = lean_ctor_get(x_145, 0);
lean_inc(x_151);
lean_dec(x_145);
x_1 = x_151;
x_6 = x_150;
goto _start;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_153 = lean_ctor_get(x_144, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_144, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_155 = x_144;
} else {
 lean_dec_ref(x_144);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_157 = lean_ctor_get(x_138, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_138, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_159 = x_138;
} else {
 lean_dec_ref(x_138);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_90);
lean_ctor_set(x_161, 1, x_91);
lean_ctor_set(x_1, 1, x_161);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_1);
lean_ctor_set(x_162, 1, x_6);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_163 = lean_ctor_get(x_1, 1);
x_164 = lean_ctor_get(x_1, 0);
lean_inc(x_163);
lean_inc(x_164);
lean_dec(x_1);
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_167 = x_163;
} else {
 lean_dec_ref(x_163);
 x_167 = lean_box(0);
}
x_168 = l_Array_isEmpty___rarg(x_166);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
lean_dec(x_167);
x_169 = l_Lean_instInhabitedExpr;
x_170 = l_Array_back___rarg(x_169, x_166);
x_171 = l_Lean_Loop_forIn_loop___at_Lean_Tactic_FunInd_mkLambdaFVarsMasked___spec__1___closed__1;
x_172 = l_Lean_Expr_isFVar(x_170);
if (x_172 == 0)
{
uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_170);
x_173 = 0;
x_174 = lean_box(x_173);
x_175 = lean_array_push(x_165, x_174);
x_176 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_177 = lean_apply_9(x_171, x_164, x_175, x_166, x_176, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_180 = x_177;
} else {
 lean_dec_ref(x_177);
 x_180 = lean_box(0);
}
x_181 = lean_ctor_get(x_178, 0);
lean_inc(x_181);
lean_dec(x_178);
if (lean_is_scalar(x_180)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_180;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_179);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_177, 1);
lean_inc(x_183);
lean_dec(x_177);
x_184 = lean_ctor_get(x_178, 0);
lean_inc(x_184);
lean_dec(x_178);
x_1 = x_184;
x_6 = x_183;
goto _start;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_186 = lean_ctor_get(x_177, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_177, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_188 = x_177;
} else {
 lean_dec_ref(x_177);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
else
{
lean_object* x_190; uint8_t x_191; 
lean_inc(x_170);
x_190 = l_Lean_Expr_fvarId_x21(x_170);
x_191 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_190, x_164);
lean_dec(x_190);
if (x_191 == 0)
{
uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_170);
x_192 = 0;
x_193 = lean_box(x_192);
x_194 = lean_array_push(x_165, x_193);
x_195 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_196 = lean_apply_9(x_171, x_164, x_194, x_166, x_195, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_199 = x_196;
} else {
 lean_dec_ref(x_196);
 x_199 = lean_box(0);
}
x_200 = lean_ctor_get(x_197, 0);
lean_inc(x_200);
lean_dec(x_197);
if (lean_is_scalar(x_199)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_199;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_198);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_196, 1);
lean_inc(x_202);
lean_dec(x_196);
x_203 = lean_ctor_get(x_197, 0);
lean_inc(x_203);
lean_dec(x_197);
x_1 = x_203;
x_6 = x_202;
goto _start;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_205 = lean_ctor_get(x_196, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_196, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_207 = x_196;
} else {
 lean_dec_ref(x_196);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; uint8_t x_212; uint8_t x_213; lean_object* x_214; 
x_209 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
x_210 = lean_array_push(x_209, x_170);
x_211 = 0;
x_212 = 1;
x_213 = 1;
x_214 = l_Lean_Meta_mkLambdaFVars(x_210, x_164, x_211, x_212, x_213, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_box(x_212);
x_218 = lean_array_push(x_165, x_217);
x_219 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_220 = lean_apply_9(x_171, x_215, x_218, x_166, x_219, x_2, x_3, x_4, x_5, x_216);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
x_224 = lean_ctor_get(x_221, 0);
lean_inc(x_224);
lean_dec(x_221);
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_223;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_222);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_220, 1);
lean_inc(x_226);
lean_dec(x_220);
x_227 = lean_ctor_get(x_221, 0);
lean_inc(x_227);
lean_dec(x_221);
x_1 = x_227;
x_6 = x_226;
goto _start;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_229 = lean_ctor_get(x_220, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_220, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_231 = x_220;
} else {
 lean_dec_ref(x_220);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_233 = lean_ctor_get(x_214, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_214, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_235 = x_214;
} else {
 lean_dec_ref(x_214);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_234);
return x_236;
}
}
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_167)) {
 x_237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_237 = x_167;
}
lean_ctor_set(x_237, 0, x_165);
lean_ctor_set(x_237, 1, x_166);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_164);
lean_ctor_set(x_238, 1, x_237);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_6);
return x_239;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_mkLambdaFVarsMasked(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Tactic_FunInd_foldCalls___lambda__10___closed__1;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Loop_forIn_loop___at_Lean_Tactic_FunInd_mkLambdaFVarsMasked___spec__1(x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Array_reverse___rarg(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Array_reverse___rarg(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
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
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Tactic_FunInd_mkLambdaFVarsMasked___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Loop_forIn_loop___at_Lean_Tactic_FunInd_mkLambdaFVarsMasked___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_maskArray___spec__1___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_1, x_3);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 2);
lean_inc(x_13);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_4;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_9, 2);
lean_dec(x_16);
x_17 = lean_ctor_get(x_9, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = lean_array_fget(x_11, x_12);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_12, x_20);
lean_dec(x_12);
lean_ctor_set(x_9, 1, x_21);
if (x_7 == 0)
{
size_t x_22; size_t x_23; 
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
goto _start;
}
else
{
lean_object* x_25; size_t x_26; size_t x_27; 
x_25 = lean_array_push(x_10, x_19);
lean_ctor_set(x_4, 1, x_25);
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
goto _start;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
x_29 = lean_array_fget(x_11, x_12);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_12, x_30);
lean_dec(x_12);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_11);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_13);
if (x_7 == 0)
{
size_t x_33; size_t x_34; 
lean_dec(x_29);
lean_ctor_set(x_4, 0, x_32);
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_3 = x_34;
goto _start;
}
else
{
lean_object* x_36; size_t x_37; size_t x_38; 
x_36 = lean_array_push(x_10, x_29);
lean_ctor_set(x_4, 1, x_36);
lean_ctor_set(x_4, 0, x_32);
x_37 = 1;
x_38 = lean_usize_add(x_3, x_37);
x_3 = x_38;
goto _start;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_4, 0);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_4);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 2);
lean_inc(x_44);
x_45 = lean_nat_dec_lt(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 x_47 = x_40;
} else {
 lean_dec_ref(x_40);
 x_47 = lean_box(0);
}
x_48 = lean_array_fget(x_42, x_43);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_43, x_49);
lean_dec(x_43);
if (lean_is_scalar(x_47)) {
 x_51 = lean_alloc_ctor(0, 3, 0);
} else {
 x_51 = x_47;
}
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_44);
if (x_7 == 0)
{
lean_object* x_52; size_t x_53; size_t x_54; 
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
x_53 = 1;
x_54 = lean_usize_add(x_3, x_53);
x_3 = x_54;
x_4 = x_52;
goto _start;
}
else
{
lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; 
x_56 = lean_array_push(x_41, x_48);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_56);
x_58 = 1;
x_59 = lean_usize_add(x_3, x_58);
x_3 = x_59;
x_4 = x_57;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_maskArray___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_maskArray___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_maskArray___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_toSubarray___rarg(x_2, x_4, x_3);
x_6 = l_Lean_Tactic_FunInd_foldCalls___lambda__10___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_array_get_size(x_1);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_maskArray___spec__1___rarg(x_1, x_9, x_10, x_7);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_maskArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_maskArray___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_maskArray___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_maskArray___spec__1___rarg(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_maskArray___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Tactic_FunInd_maskArray___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_buildInductionBody___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_unbox(x_5);
lean_dec(x_5);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_array_uset(x_7, x_2, x_12);
x_2 = x_9;
x_3 = x_13;
goto _start;
}
else
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_array_uset(x_7, x_2, x_16);
x_2 = x_9;
x_3 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Tactic_FunInd_buildInductionBody___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_5, x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_4, x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_Tactic_FunInd_collectIHs(x_1, x_2, x_3, x_14, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Array_append___rarg(x_7, x_16);
x_19 = 1;
x_20 = lean_usize_add(x_5, x_19);
x_5 = x_20;
x_7 = x_18;
x_12 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Tactic_FunInd_buildInductionCase(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_expr_instantiate1(x_1, x_10);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_17 = l_Lean_Tactic_FunInd_buildInductionBody(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_mkLetFun(x_10, x_9, x_18, x_11, x_12, x_13, x_14, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_8);
x_15 = l_Lean_Expr_letFun_x3f(x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Tactic_FunInd_buildInductionCase(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_8);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_22);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_24 = l_Lean_Tactic_FunInd_collectIHs(x_1, x_2, x_3, x_22, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Array_append___rarg(x_7, x_25);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_1);
x_28 = l_Lean_Tactic_FunInd_foldCalls(x_1, x_2, x_21, x_10, x_11, x_12, x_13, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_1);
x_31 = l_Lean_Tactic_FunInd_foldCalls(x_1, x_2, x_22, x_10, x_11, x_12, x_13, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_buildInductionBody___lambda__2___boxed), 15, 9);
lean_closure_set(x_34, 0, x_23);
lean_closure_set(x_34, 1, x_1);
lean_closure_set(x_34, 2, x_4);
lean_closure_set(x_34, 3, x_5);
lean_closure_set(x_34, 4, x_6);
lean_closure_set(x_34, 5, x_2);
lean_closure_set(x_34, 6, x_3);
lean_closure_set(x_34, 7, x_27);
lean_closure_set(x_34, 8, x_32);
x_35 = 0;
x_36 = 0;
x_37 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_20, x_35, x_29, x_34, x_36, x_10, x_11, x_12, x_13, x_33);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_31);
if (x_46 == 0)
{
return x_31;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_31, 0);
x_48 = lean_ctor_get(x_31, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_31);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_28);
if (x_50 == 0)
{
return x_28;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_28, 0);
x_52 = lean_ctor_get(x_28, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_28);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_24);
if (x_54 == 0)
{
return x_24;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_24, 0);
x_56 = lean_ctor_get(x_24, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_24);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_expr_instantiate1(x_1, x_9);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_16 = l_Lean_Tactic_FunInd_buildInductionBody(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
x_20 = lean_array_push(x_19, x_9);
x_21 = 0;
x_22 = 1;
x_23 = 1;
x_24 = l_Lean_Meta_mkLambdaFVars(x_20, x_17, x_21, x_22, x_23, x_10, x_11, x_12, x_13, x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_dec(x_9);
if (lean_obj_tag(x_8) == 8)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 3);
lean_inc(x_18);
lean_dec(x_8);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Lean_Tactic_FunInd_collectIHs(x_1, x_2, x_3, x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Array_append___rarg(x_7, x_20);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_Lean_Tactic_FunInd_foldCalls(x_1, x_2, x_16, x_10, x_11, x_12, x_13, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_1);
x_26 = l_Lean_Tactic_FunInd_foldCalls(x_1, x_2, x_17, x_10, x_11, x_12, x_13, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_buildInductionBody___lambda__4___boxed), 14, 8);
lean_closure_set(x_29, 0, x_18);
lean_closure_set(x_29, 1, x_1);
lean_closure_set(x_29, 2, x_4);
lean_closure_set(x_29, 3, x_5);
lean_closure_set(x_29, 4, x_6);
lean_closure_set(x_29, 5, x_2);
lean_closure_set(x_29, 6, x_3);
lean_closure_set(x_29, 7, x_22);
x_30 = 0;
x_31 = l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___spec__1___rarg(x_15, x_24, x_27, x_29, x_30, x_10, x_11, x_12, x_13, x_28);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_26);
if (x_40 == 0)
{
return x_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_26, 0);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_26);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_23);
if (x_44 == 0)
{
return x_23;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_23, 0);
x_46 = lean_ctor_get(x_23, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_23);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_19);
if (x_48 == 0)
{
return x_19;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_19, 0);
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_19);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_box(0);
x_53 = l_Lean_Tactic_FunInd_buildInductionBody___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_52, x_10, x_11, x_12, x_13, x_14);
return x_53;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Tactic_FunInd_maskArray___rarg(x_1, x_3);
x_11 = l_Lean_Expr_beta(x_2, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_buildInductionBody___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Tactic.FunInd.buildInductionBody", 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_buildInductionBody___lambda__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__1;
x_2 = l_Lean_Tactic_FunInd_buildInductionBody___lambda__7___closed__1;
x_3 = lean_unsigned_to_nat(479u);
x_4 = lean_unsigned_to_nat(40u);
x_5 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_array_get_size(x_7);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Tactic_FunInd_buildInductionBody___lambda__7___closed__2;
x_18 = l_panic___at_Lean_Meta_whnfCore_go___spec__1(x_17, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_fget(x_7, x_19);
lean_inc(x_20);
x_21 = l_Lean_Expr_fvarId_x21(x_20);
lean_inc(x_21);
x_22 = lean_array_push(x_1, x_21);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_23 = l_Lean_Tactic_FunInd_buildInductionBody(x_2, x_22, x_3, x_8, x_4, x_21, x_5, x_6, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
x_27 = lean_array_push(x_26, x_20);
x_28 = 0;
x_29 = 1;
x_30 = 1;
x_31 = l_Lean_Meta_mkLambdaFVars(x_27, x_24, x_28, x_29, x_30, x_9, x_10, x_11, x_12, x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_23);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_buildInductionBody___lambda__7___boxed), 13, 6);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_6);
lean_closure_set(x_13, 4, x_4);
lean_closure_set(x_13, 5, x_7);
x_14 = l_Lean_Tactic_FunInd_collectIHs___lambda__10___closed__1;
x_15 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__5___rarg(x_5, x_14, x_13, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_buildInductionBody___lambda__8), 12, 5);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
x_13 = l_Lean_Tactic_FunInd_removeLamda___rarg(x_6, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Tactic_FunInd_buildInductionBody(x_1, x_2, x_3, x_7, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_buildInductionBody___lambda__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_pure___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___rarg___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_1, 9);
lean_inc(x_17);
x_18 = l_Array_isEmpty___rarg(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_apply_6(x_2, x_19, x_12, x_13, x_14, x_15, x_16);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_21 = l_Lean_Tactic_FunInd_mkLambdaFVarsMasked(x_3, x_4, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_array_get_size(x_24);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = 0;
lean_inc(x_24);
x_29 = l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_buildInductionBody___spec__1(x_27, x_28, x_24);
lean_inc(x_6);
lean_inc(x_5);
x_30 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_foldCalls), 8, 2);
lean_closure_set(x_30, 0, x_5);
lean_closure_set(x_30, 1, x_6);
x_31 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_buildInductionBody___lambda__6___boxed), 9, 2);
lean_closure_set(x_31, 0, x_24);
lean_closure_set(x_31, 1, x_25);
x_32 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_buildInductionBody___lambda__10), 13, 6);
lean_closure_set(x_32, 0, x_5);
lean_closure_set(x_32, 1, x_7);
lean_closure_set(x_32, 2, x_8);
lean_closure_set(x_32, 3, x_6);
lean_closure_set(x_32, 4, x_9);
lean_closure_set(x_32, 5, x_10);
x_33 = 1;
x_34 = l_Lean_Tactic_FunInd_buildInductionBody___lambda__11___closed__1;
x_35 = l_Lean_Meta_MatcherApp_transform(x_1, x_33, x_29, x_30, x_31, x_32, x_34, x_12, x_13, x_14, x_15, x_23);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = l_Lean_Meta_MatcherApp_toExpr(x_37);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = l_Lean_Meta_MatcherApp_toExpr(x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
return x_35;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_35, 0);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_35);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_21);
if (x_47 == 0)
{
return x_21;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_21, 0);
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_21);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
lean_dec(x_9);
x_15 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_16 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1(x_1, x_15, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = l_Lean_Tactic_FunInd_buildInductionBody___lambda__5(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_1, x_19, x_10, x_11, x_12, x_13, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_buildInductionBody___lambda__5), 14, 8);
lean_closure_set(x_23, 0, x_2);
lean_closure_set(x_23, 1, x_3);
lean_closure_set(x_23, 2, x_4);
lean_closure_set(x_23, 3, x_5);
lean_closure_set(x_23, 4, x_6);
lean_closure_set(x_23, 5, x_7);
lean_closure_set(x_23, 6, x_8);
lean_closure_set(x_23, 7, x_1);
x_24 = lean_ctor_get(x_22, 4);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 6);
lean_inc(x_25);
lean_inc(x_25);
x_26 = l_Array_append___rarg(x_24, x_25);
x_27 = lean_array_get_size(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_lt(x_28, x_27);
if (x_29 == 0)
{
lean_object* x_93; 
lean_dec(x_27);
lean_dec(x_26);
x_93 = l_Lean_Tactic_FunInd_foldCalls___lambda__10___closed__1;
x_30 = x_93;
x_31 = x_21;
goto block_92;
}
else
{
uint8_t x_94; 
x_94 = lean_nat_dec_le(x_27, x_27);
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_27);
lean_dec(x_26);
x_95 = l_Lean_Tactic_FunInd_foldCalls___lambda__10___closed__1;
x_30 = x_95;
x_31 = x_21;
goto block_92;
}
else
{
size_t x_96; size_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = 0;
x_97 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_98 = l_Lean_Tactic_FunInd_foldCalls___lambda__10___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_99 = l_Array_foldlMUnsafe_fold___at_Lean_Tactic_FunInd_buildInductionBody___spec__2(x_2, x_3, x_4, x_26, x_96, x_97, x_98, x_10, x_11, x_12, x_13, x_21);
lean_dec(x_26);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_30 = x_100;
x_31 = x_101;
goto block_92;
}
else
{
uint8_t x_102; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_102 = !lean_is_exclusive(x_99);
if (x_102 == 0)
{
return x_99;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_99, 0);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_99);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
block_92:
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Array_append___rarg(x_8, x_30);
lean_inc(x_10);
lean_inc(x_4);
x_33 = l_Lean_FVarId_getType(x_4, x_10, x_11, x_12, x_13, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_7);
x_36 = l_Lean_mkArrow(x_34, x_7, x_12, x_13, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_25);
x_39 = l_Lean_Tactic_FunInd_mkLambdaFVarsMasked(x_25, x_37, x_10, x_11, x_12, x_13, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_66 = lean_ctor_get(x_22, 9);
lean_inc(x_66);
x_67 = lean_array_get_size(x_66);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_dec_eq(x_67, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_43);
lean_dec(x_42);
x_70 = lean_box(0);
x_71 = l_Lean_Tactic_FunInd_buildInductionBody___lambda__11(x_22, x_23, x_25, x_7, x_2, x_3, x_5, x_6, x_4, x_32, x_70, x_10, x_11, x_12, x_13, x_41);
return x_71;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_lt(x_28, x_67);
lean_dec(x_67);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec(x_66);
x_73 = l_Lean_instInhabitedExpr;
x_74 = l___private_Init_Util_0__outOfBounds___rarg(x_73);
x_75 = l_Lean_Expr_isFVarOf(x_74, x_3);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_43);
lean_dec(x_42);
x_76 = lean_box(0);
x_77 = l_Lean_Tactic_FunInd_buildInductionBody___lambda__11(x_22, x_23, x_25, x_7, x_2, x_3, x_5, x_6, x_4, x_32, x_76, x_10, x_11, x_12, x_13, x_41);
return x_77;
}
else
{
lean_object* x_78; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_7);
x_78 = lean_box(0);
x_44 = x_78;
goto block_65;
}
}
else
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_array_fget(x_66, x_28);
lean_dec(x_66);
x_80 = l_Lean_Expr_isFVarOf(x_79, x_3);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_43);
lean_dec(x_42);
x_81 = lean_box(0);
x_82 = l_Lean_Tactic_FunInd_buildInductionBody___lambda__11(x_22, x_23, x_25, x_7, x_2, x_3, x_5, x_6, x_4, x_32, x_81, x_10, x_11, x_12, x_13, x_41);
return x_82;
}
else
{
lean_object* x_83; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_7);
x_83 = lean_box(0);
x_44 = x_83;
goto block_65;
}
}
}
block_65:
{
lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_44);
x_45 = lean_array_get_size(x_42);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_47 = 0;
lean_inc(x_42);
x_48 = l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_buildInductionBody___spec__1(x_46, x_47, x_42);
lean_inc(x_2);
x_49 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_foldCalls), 8, 2);
lean_closure_set(x_49, 0, x_2);
lean_closure_set(x_49, 1, x_3);
x_50 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_buildInductionBody___lambda__6___boxed), 9, 2);
lean_closure_set(x_50, 0, x_42);
lean_closure_set(x_50, 1, x_43);
x_51 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_buildInductionBody___lambda__9), 11, 4);
lean_closure_set(x_51, 0, x_5);
lean_closure_set(x_51, 1, x_2);
lean_closure_set(x_51, 2, x_6);
lean_closure_set(x_51, 3, x_32);
x_52 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_collectIHs___lambda__12___boxed), 7, 1);
lean_closure_set(x_52, 0, x_4);
x_53 = l_Lean_Meta_MatcherApp_transform(x_22, x_15, x_48, x_49, x_50, x_51, x_52, x_10, x_11, x_12, x_13, x_41);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = l_Lean_Meta_MatcherApp_toExpr(x_55);
lean_ctor_set(x_53, 0, x_56);
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_53);
x_59 = l_Lean_Meta_MatcherApp_toExpr(x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_53);
if (x_61 == 0)
{
return x_53;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_53, 0);
x_63 = lean_ctor_get(x_53, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_53);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_39);
if (x_84 == 0)
{
return x_39;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_39, 0);
x_86 = lean_ctor_get(x_39, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_39);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_33);
if (x_88 == 0)
{
return x_33;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_33, 0);
x_90 = lean_ctor_get(x_33, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_33);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_16);
if (x_106 == 0)
{
return x_16;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_16, 0);
x_108 = lean_ctor_get(x_16, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_16);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
lean_inc(x_9);
x_16 = lean_array_push(x_15, x_9);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_18 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux(x_16, x_17, x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Expr_fvarId_x21(x_9);
x_22 = lean_array_push(x_2, x_21);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_23 = l_Lean_Tactic_FunInd_buildInductionBody(x_3, x_4, x_22, x_5, x_6, x_7, x_8, x_19, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 0;
x_27 = 1;
x_28 = 1;
x_29 = l_Lean_Meta_mkLambdaFVars(x_16, x_24, x_26, x_27, x_28, x_10, x_11, x_12, x_13, x_25);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_18);
if (x_34 == 0)
{
return x_18;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_18, 0);
x_36 = lean_ctor_get(x_18, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_18);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_buildInductionBody___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__1;
x_2 = l_Lean_Tactic_FunInd_buildInductionBody___lambda__7___closed__1;
x_3 = lean_unsigned_to_nat(444u);
x_4 = lean_unsigned_to_nat(44u);
x_5 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_buildInductionBody___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("h", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_buildInductionBody___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Tactic_FunInd_buildInductionBody___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_buildInductionBody___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("dite", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_buildInductionBody___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Tactic_FunInd_buildInductionBody___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isDIte(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_Tactic_FunInd_buildInductionBody___lambda__12(x_8, x_1, x_5, x_6, x_2, x_3, x_4, x_7, x_15, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_8, x_17);
x_19 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__1;
lean_inc(x_18);
x_20 = lean_mk_array(x_18, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_18, x_21);
lean_dec(x_18);
lean_inc(x_8);
x_23 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_8, x_20, x_22);
x_24 = lean_array_get_size(x_23);
x_25 = lean_unsigned_to_nat(5u);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
x_27 = l_Lean_Tactic_FunInd_buildInductionBody___closed__1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_28 = l_panic___at___private_Lean_Meta_WHNF_0__Lean_Meta_cache___spec__1(x_27, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Tactic_FunInd_buildInductionBody___lambda__12(x_8, x_1, x_5, x_6, x_2, x_3, x_4, x_7, x_29, x_9, x_10, x_11, x_12, x_30);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_11);
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
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_8);
x_36 = lean_array_fget(x_23, x_21);
x_37 = lean_unsigned_to_nat(2u);
x_38 = lean_array_fget(x_23, x_37);
x_39 = lean_unsigned_to_nat(3u);
x_40 = lean_array_fget(x_23, x_39);
x_41 = lean_unsigned_to_nat(4u);
x_42 = lean_array_fget(x_23, x_41);
lean_dec(x_23);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_36);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_43 = l_Lean_Tactic_FunInd_collectIHs(x_1, x_5, x_6, x_36, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Array_append___rarg(x_7, x_44);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_1);
x_47 = l_Lean_Tactic_FunInd_foldCalls(x_1, x_5, x_36, x_9, x_10, x_11, x_12, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_1);
x_50 = l_Lean_Tactic_FunInd_foldCalls(x_1, x_5, x_38, x_9, x_10, x_11, x_12, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_46);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_53 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_buildInductionBody___lambda__13), 14, 8);
lean_closure_set(x_53, 0, x_40);
lean_closure_set(x_53, 1, x_3);
lean_closure_set(x_53, 2, x_1);
lean_closure_set(x_53, 3, x_2);
lean_closure_set(x_53, 4, x_4);
lean_closure_set(x_53, 5, x_5);
lean_closure_set(x_53, 6, x_6);
lean_closure_set(x_53, 7, x_46);
x_54 = l_Lean_Tactic_FunInd_buildInductionBody___closed__3;
x_55 = 0;
x_56 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_48);
x_57 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_54, x_55, x_48, x_53, x_56, x_9, x_10, x_11, x_12, x_52);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_48);
x_60 = l_Lean_mkNot(x_48);
lean_inc(x_4);
x_61 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_buildInductionBody___lambda__13), 14, 8);
lean_closure_set(x_61, 0, x_42);
lean_closure_set(x_61, 1, x_3);
lean_closure_set(x_61, 2, x_1);
lean_closure_set(x_61, 3, x_2);
lean_closure_set(x_61, 4, x_4);
lean_closure_set(x_61, 5, x_5);
lean_closure_set(x_61, 6, x_6);
lean_closure_set(x_61, 7, x_46);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_62 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_54, x_55, x_60, x_61, x_56, x_9, x_10, x_11, x_12, x_59);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_4);
x_65 = l_Lean_Meta_getLevel(x_4, x_9, x_10, x_11, x_12, x_64);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Tactic_FunInd_buildInductionBody___closed__5;
x_71 = l_Lean_Expr_const___override(x_70, x_69);
x_72 = l_Lean_mkApp5(x_71, x_4, x_48, x_51, x_58, x_63);
lean_ctor_set(x_65, 0, x_72);
return x_65;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_73 = lean_ctor_get(x_65, 0);
x_74 = lean_ctor_get(x_65, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_65);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Tactic_FunInd_buildInductionBody___closed__5;
x_78 = l_Lean_Expr_const___override(x_77, x_76);
x_79 = l_Lean_mkApp5(x_78, x_4, x_48, x_51, x_58, x_63);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_74);
return x_80;
}
}
else
{
uint8_t x_81; 
lean_dec(x_63);
lean_dec(x_58);
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_4);
x_81 = !lean_is_exclusive(x_65);
if (x_81 == 0)
{
return x_65;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_65, 0);
x_83 = lean_ctor_get(x_65, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_65);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_58);
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_85 = !lean_is_exclusive(x_62);
if (x_85 == 0)
{
return x_62;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_62, 0);
x_87 = lean_ctor_get(x_62, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_62);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_42);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_57);
if (x_89 == 0)
{
return x_57;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_57, 0);
x_91 = lean_ctor_get(x_57, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_57);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_50);
if (x_93 == 0)
{
return x_50;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_50, 0);
x_95 = lean_ctor_get(x_50, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_50);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_46);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_47);
if (x_97 == 0)
{
return x_47;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_47, 0);
x_99 = lean_ctor_get(x_47, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_47);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_43);
if (x_101 == 0)
{
return x_43;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_43, 0);
x_103 = lean_ctor_get(x_43, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_43);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_buildInductionBody___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_buildInductionBody___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Tactic_FunInd_buildInductionBody___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Tactic_FunInd_buildInductionBody___spec__2(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Tactic_FunInd_buildInductionBody___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Tactic_FunInd_buildInductionBody___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Tactic_FunInd_buildInductionBody___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Tactic_FunInd_buildInductionBody___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Tactic_FunInd_buildInductionBody___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Tactic_FunInd_buildInductionBody___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_buildInductionBody___lambda__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Tactic_FunInd_buildInductionBody___lambda__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_findFixF___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_findFixF___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Tactic_FunInd_findFixF___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Array_append___rarg(x_1, x_3);
x_11 = lean_apply_7(x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("WellFounded", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fixF", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__1;
x_2 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fix", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__1;
x_2 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Function ", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" does not look like a function defined by well-founded ", 55);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("recursion.\nNB: If ", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" is not itself recursive, but contains an inner recursive ", 58);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("function (via `let rec` or `where`), try `", 42);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".go` where `go` is name of the inner ", 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__16;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("function.", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__18;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__19;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__3;
x_11 = l_Lean_Expr_isAppOf(x_4, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__5;
x_13 = l_Lean_Expr_isAppOf(x_4, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = l_Lean_MessageData_ofName(x_1);
x_15 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__7;
lean_inc(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__9;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__11;
lean_inc(x_14);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
x_21 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__13;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__15;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_14);
x_26 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__17;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__20;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at_Lean_Tactic_FunInd_findFixF___spec__1___rarg(x_30, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_31;
}
else
{
lean_object* x_32; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_32 = l_Lean_Meta_unfoldDefinition(x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__1), 9, 2);
lean_closure_set(x_35, 0, x_3);
lean_closure_set(x_35, 1, x_2);
x_36 = l_Lean_Tactic_FunInd_findFixF___rarg(x_1, x_33, x_35, x_5, x_6, x_7, x_8, x_34);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_1);
x_41 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_findFixF___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2), 9, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
x_10 = 0;
x_11 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg(x_2, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_findFixF(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_findFixF___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_findFixF___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Tactic_FunInd_findFixF___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Environment_contains(x_10, x_1);
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Environment_contains(x_15, x_1);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is not a definition", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_box(0);
x_17 = l_Lean_Expr_const___override(x_1, x_16);
x_18 = l_Lean_MessageData_ofExpr(x_17);
x_19 = l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__3(x_22, x_2, x_3, x_4, x_5, x_15);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Tactic_FunInd_collectIHs___spec__1___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
lean_inc(x_1);
x_15 = l_Lean_Expr_fvarId_x21(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_15);
x_16 = l_Lean_Tactic_FunInd_substVarAfter(x_12, x_15, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_Lean_MVarId_revertAfter(x_17, x_15, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_14, x_3, x_22);
x_3 = x_24;
x_4 = x_25;
x_9 = x_21;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_getType(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("case", 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
x_11 = lean_array_fget(x_2, x_4);
x_12 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
lean_inc(x_12);
x_13 = l_Nat_repr(x_12);
x_14 = l_Array_mapIdxM_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__7___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_box(0);
x_19 = l_Lean_Name_str___override(x_18, x_17);
x_20 = lean_alloc_closure((void*)(l_Array_mapIdxM_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__7___lambda__1___boxed), 7, 1);
lean_closure_set(x_20, 0, x_11);
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_array_push(x_6, x_24);
x_3 = x_10;
x_4 = x_12;
x_5 = lean_box(0);
x_6 = x_25;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_st_ref_take(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_10, 7);
x_16 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_15, x_1, x_2);
lean_ctor_set(x_10, 7, x_16);
x_17 = lean_st_ref_set(x_4, x_9, x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
x_26 = lean_ctor_get(x_10, 2);
x_27 = lean_ctor_get(x_10, 3);
x_28 = lean_ctor_get(x_10, 4);
x_29 = lean_ctor_get(x_10, 5);
x_30 = lean_ctor_get(x_10, 6);
x_31 = lean_ctor_get(x_10, 7);
x_32 = lean_ctor_get(x_10, 8);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_33 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_31, x_1, x_2);
x_34 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_26);
lean_ctor_set(x_34, 3, x_27);
lean_ctor_set(x_34, 4, x_28);
lean_ctor_set(x_34, 5, x_29);
lean_ctor_set(x_34, 6, x_30);
lean_ctor_set(x_34, 7, x_33);
lean_ctor_set(x_34, 8, x_32);
lean_ctor_set(x_9, 0, x_34);
x_35 = lean_st_ref_set(x_4, x_9, x_11);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = lean_box(0);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_40 = lean_ctor_get(x_9, 1);
x_41 = lean_ctor_get(x_9, 2);
x_42 = lean_ctor_get(x_9, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_9);
x_43 = lean_ctor_get(x_10, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_10, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_10, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_10, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_10, 5);
lean_inc(x_48);
x_49 = lean_ctor_get(x_10, 6);
lean_inc(x_49);
x_50 = lean_ctor_get(x_10, 7);
lean_inc(x_50);
x_51 = lean_ctor_get(x_10, 8);
lean_inc(x_51);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 lean_ctor_release(x_10, 4);
 lean_ctor_release(x_10, 5);
 lean_ctor_release(x_10, 6);
 lean_ctor_release(x_10, 7);
 lean_ctor_release(x_10, 8);
 x_52 = x_10;
} else {
 lean_dec_ref(x_10);
 x_52 = lean_box(0);
}
x_53 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_50, x_1, x_2);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 9, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_44);
lean_ctor_set(x_54, 2, x_45);
lean_ctor_set(x_54, 3, x_46);
lean_ctor_set(x_54, 4, x_47);
lean_ctor_set(x_54, 5, x_48);
lean_ctor_set(x_54, 6, x_49);
lean_ctor_set(x_54, 7, x_53);
lean_ctor_set(x_54, 8, x_51);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_40);
lean_ctor_set(x_55, 2, x_41);
lean_ctor_set(x_55, 3, x_42);
x_56 = lean_st_ref_set(x_4, x_55, x_11);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
x_59 = lean_box(0);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_array_uget(x_1, x_3);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
x_19 = lean_ctor_get(x_4, 2);
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_4, 0);
lean_dec(x_21);
x_22 = lean_array_fget(x_13, x_14);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_14, x_23);
lean_dec(x_14);
lean_ctor_set(x_4, 1, x_24);
x_25 = l_Lean_MVarId_assign___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__8(x_12, x_22, x_5, x_6, x_7, x_8, x_9);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = 1;
x_28 = lean_usize_add(x_3, x_27);
x_3 = x_28;
x_9 = x_26;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_4);
x_30 = lean_array_fget(x_13, x_14);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_14, x_31);
lean_dec(x_14);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_15);
x_34 = l_Lean_MVarId_assign___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__8(x_12, x_30, x_5, x_6, x_7, x_8, x_9);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = 1;
x_37 = lean_usize_add(x_3, x_36);
x_3 = x_37;
x_4 = x_33;
x_9 = x_35;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__11___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_push(x_1, x_5);
x_12 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__11___rarg(x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_lt(x_10, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_apply_6(x_2, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_array_fget(x_1, x_10);
lean_dec(x_10);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = lean_apply_6(x_18, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecls_loop___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__11___rarg___lambda__1), 10, 4);
lean_closure_set(x_22, 0, x_4);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_3);
x_23 = 0;
x_24 = lean_unbox(x_17);
lean_dec(x_17);
x_25 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_16, x_24, x_20, x_22, x_23, x_5, x_6, x_7, x_8, x_21);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecls_loop___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__11___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Tactic_FunInd_foldCalls___lambda__10___closed__1;
x_10 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__11___rarg(x_2, x_3, x_1, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecls___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__10___rarg), 8, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_10 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__1___closed__1;
x_11 = lean_array_push(x_10, x_1);
x_12 = lean_array_push(x_11, x_2);
x_13 = 0;
x_14 = 1;
x_15 = 1;
x_16 = l_Lean_Meta_mkLambdaFVars(x_12, x_3, x_13, x_14, x_15, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Did not fully eliminate ", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" from induction principle body:", 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_1);
x_13 = l_Lean_Expr_fvarId_x21(x_1);
lean_inc(x_13);
x_14 = lean_array_push(x_2, x_13);
lean_inc(x_4);
x_15 = l_Lean_Expr_app___override(x_3, x_4);
x_16 = l_Lean_Tactic_FunInd_foldCalls___lambda__10___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Tactic_FunInd_buildInductionBody(x_5, x_14, x_16, x_15, x_6, x_13, x_16, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_6, x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_6);
x_21 = lean_box(0);
x_22 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__1(x_4, x_1, x_18, x_21, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_1);
x_23 = l_Lean_Expr_fvar___override(x_6);
x_24 = l_Lean_MessageData_ofExpr(x_23);
x_25 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__2;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__4;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_indentExpr(x_7);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_32, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Tactic.FunInd.deriveUnaryInduction", 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__1;
x_2 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__3___closed__1;
x_3 = lean_unsigned_to_nat(556u);
x_4 = lean_unsigned_to_nat(34u);
x_5 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_get_size(x_4);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__3___closed__2;
x_15 = l_panic___at_Lean_Meta_whnfCore_go___spec__1(x_14, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fget(x_4, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_array_fget(x_4, x_18);
x_20 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
lean_inc(x_17);
x_21 = lean_array_push(x_20, x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux(x_21, x_16, x_1, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2), 12, 5);
lean_closure_set(x_25, 0, x_19);
lean_closure_set(x_25, 1, x_20);
lean_closure_set(x_25, 2, x_2);
lean_closure_set(x_25, 3, x_17);
lean_closure_set(x_25, 4, x_3);
x_26 = l_Lean_Tactic_FunInd_removeLamda___rarg(x_23, x_25, x_6, x_7, x_8, x_9, x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__4(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_11 = lean_array_get_size(x_5);
x_12 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_13 = l_Array_toSubarray___rarg(x_5, x_12, x_11);
x_14 = lean_usize_of_nat(x_1);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__9(x_2, x_14, x_3, x_13, x_6, x_7, x_8, x_9, x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_4, x_6, x_7, x_8, x_9, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 0;
x_21 = 1;
x_22 = 1;
x_23 = l_Lean_Meta_mkLambdaFVars(x_5, x_18, x_20, x_21, x_22, x_6, x_7, x_8, x_9, x_19);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_3);
lean_inc(x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_4);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_addDecl(x_15, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelZero;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_elimOptParam___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_elimOptParam___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to derive induction priciple:", 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_box(0);
x_19 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__1;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__3;
x_22 = l_Lean_Expr_const___override(x_21, x_20);
lean_inc(x_12);
x_23 = l_Lean_mkApp3(x_22, x_2, x_3, x_12);
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
lean_dec(x_4);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_25);
x_26 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_25, x_18);
x_27 = l_Lean_Expr_const___override(x_5, x_26);
x_28 = lean_array_pop(x_6);
lean_inc(x_28);
x_29 = l_Lean_mkAppN(x_27, x_28);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_23);
x_30 = lean_infer_type(x_23, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Expr_bindingDomain_x21(x_31);
lean_dec(x_31);
lean_inc(x_12);
x_34 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__3___boxed), 10, 3);
lean_closure_set(x_34, 0, x_7);
lean_closure_set(x_34, 1, x_12);
lean_closure_set(x_34, 2, x_29);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_35 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_33, x_34, x_13, x_14, x_15, x_16, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_mkApp3(x_23, x_36, x_8, x_9);
x_39 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
x_40 = lean_array_push(x_39, x_10);
x_41 = 0;
x_42 = 1;
x_43 = 1;
x_44 = l_Lean_Meta_mkLambdaFVars(x_40, x_38, x_41, x_42, x_43, x_13, x_14, x_15, x_16, x_37);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_45);
x_47 = l_Lean_Meta_getMVarsNoDelayed(x_45, x_13, x_14, x_15, x_16, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_array_get_size(x_48);
x_51 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_52 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_53 = l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__6(x_12, x_51, x_52, x_48, x_13, x_14, x_15, x_16, x_49);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_array_get_size(x_54);
x_57 = lean_mk_empty_array_with_capacity(x_56);
x_58 = lean_unsigned_to_nat(0u);
lean_inc(x_56);
x_59 = l_Array_mapIdxM_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__7(x_54, x_54, x_56, x_58, lean_box(0), x_57);
x_60 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___boxed__const__1;
x_61 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__4___boxed), 10, 4);
lean_closure_set(x_61, 0, x_56);
lean_closure_set(x_61, 1, x_54);
lean_closure_set(x_61, 2, x_60);
lean_closure_set(x_61, 3, x_45);
x_62 = l_Lean_instInhabitedExpr;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_63 = l_Lean_Meta_withLocalDecls___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__10___rarg(x_62, x_59, x_61, x_13, x_14, x_15, x_16, x_55);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_array_push(x_39, x_12);
x_67 = l_Array_append___rarg(x_28, x_66);
x_68 = 0;
x_69 = l_Lean_Meta_mkLambdaFVars(x_67, x_64, x_41, x_42, x_68, x_13, x_14, x_15, x_16, x_65);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_70, x_13, x_14, x_15, x_16, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_73);
x_75 = lean_infer_type(x_73, x_13, x_14, x_15, x_16, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__2;
x_79 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__3;
lean_inc(x_16);
lean_inc(x_15);
x_80 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_76, x_78, x_79, x_15, x_16, x_77);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_73);
x_83 = l_Lean_Meta_isTypeCorrect(x_73, x_13, x_14, x_15, x_16, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
lean_inc(x_73);
x_87 = l_Lean_indentExpr(x_73);
x_88 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__5;
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_90 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = 2;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_93 = l_Lean_log___at_Lean_Meta_computeSynthOrder___spec__6(x_91, x_92, x_13, x_14, x_15, x_16, x_86);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_73);
x_95 = l_Lean_Meta_check(x_73, x_13, x_14, x_15, x_16, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__5(x_11, x_25, x_81, x_18, x_73, x_96, x_13, x_14, x_15, x_16, x_97);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_96);
return x_98;
}
else
{
uint8_t x_99; 
lean_dec(x_81);
lean_dec(x_73);
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_99 = !lean_is_exclusive(x_95);
if (x_99 == 0)
{
return x_95;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_95, 0);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_95);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_83, 1);
lean_inc(x_103);
lean_dec(x_83);
x_104 = lean_box(0);
x_105 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__5(x_11, x_25, x_81, x_18, x_73, x_104, x_13, x_14, x_15, x_16, x_103);
lean_dec(x_14);
lean_dec(x_13);
return x_105;
}
}
else
{
uint8_t x_106; 
lean_dec(x_81);
lean_dec(x_73);
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_106 = !lean_is_exclusive(x_83);
if (x_106 == 0)
{
return x_83;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_83, 0);
x_108 = lean_ctor_get(x_83, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_83);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_73);
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_110 = !lean_is_exclusive(x_80);
if (x_110 == 0)
{
return x_80;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_80, 0);
x_112 = lean_ctor_get(x_80, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_80);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_73);
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_114 = !lean_is_exclusive(x_75);
if (x_114 == 0)
{
return x_75;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_75, 0);
x_116 = lean_ctor_get(x_75, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_75);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_118 = !lean_is_exclusive(x_69);
if (x_118 == 0)
{
return x_69;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_69, 0);
x_120 = lean_ctor_get(x_69, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_69);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_122 = !lean_is_exclusive(x_63);
if (x_122 == 0)
{
return x_63;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_63, 0);
x_124 = lean_ctor_get(x_63, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_63);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_45);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_126 = !lean_is_exclusive(x_53);
if (x_126 == 0)
{
return x_53;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_53, 0);
x_128 = lean_ctor_get(x_53, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_53);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_130 = !lean_is_exclusive(x_44);
if (x_130 == 0)
{
return x_44;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_44, 0);
x_132 = lean_ctor_get(x_44, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_44);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_134 = !lean_is_exclusive(x_35);
if (x_134 == 0)
{
return x_35;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_35, 0);
x_136 = lean_ctor_get(x_35, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_35);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_138 = !lean_is_exclusive(x_30);
if (x_138 == 0)
{
return x_30;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_30, 0);
x_140 = lean_ctor_get(x_30, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_30);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__1;
x_2 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__3___closed__1;
x_3 = lean_unsigned_to_nat(548u);
x_4 = lean_unsigned_to_nat(53u);
x_5 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("motive", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Expr_constLevels_x21(x_1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__1;
x_20 = l_panic___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__5(x_19, x_13, x_14, x_15, x_16, x_17);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__1;
x_23 = l_panic___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__5(x_22, x_13, x_14, x_15, x_16, x_17);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__1;
lean_inc(x_2);
x_27 = l_Lean_mkArrow(x_2, x_26, x_15, x_16, x_17);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___boxed), 17, 11);
lean_closure_set(x_30, 0, x_25);
lean_closure_set(x_30, 1, x_2);
lean_closure_set(x_30, 2, x_3);
lean_closure_set(x_30, 3, x_4);
lean_closure_set(x_30, 4, x_5);
lean_closure_set(x_30, 5, x_6);
lean_closure_set(x_30, 6, x_7);
lean_closure_set(x_30, 7, x_8);
lean_closure_set(x_30, 8, x_9);
lean_closure_set(x_30, 9, x_10);
lean_closure_set(x_30, 10, x_11);
x_31 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__3;
x_32 = 0;
x_33 = 0;
x_34 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_31, x_32, x_28, x_30, x_33, x_13, x_14, x_15, x_16, x_29);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__1;
x_36 = l_panic___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__5(x_35, x_13, x_14, x_15, x_16, x_17);
return x_36;
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Application of WellFounded.fixF has wrong arity ", 48);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fixF application argument ", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" is not function argument ", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_7);
x_13 = lean_array_get_size(x_1);
x_14 = lean_unsigned_to_nat(6u);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Nat_repr(x_13);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__4(x_22, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_13);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_array_fget(x_1, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_array_fget(x_1, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_array_fget(x_1, x_28);
x_30 = lean_unsigned_to_nat(4u);
x_31 = lean_array_fget(x_1, x_30);
x_32 = lean_unsigned_to_nat(5u);
x_33 = lean_array_fget(x_1, x_32);
lean_dec(x_1);
x_34 = l_Lean_instInhabitedExpr;
x_35 = l_Array_back___rarg(x_34, x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_35);
lean_inc(x_31);
x_36 = l_Lean_Meta_isExprDefEq(x_31, x_35, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_MessageData_ofExpr(x_31);
x_41 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__4;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__6;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_44, x_8, x_9, x_10, x_11, x_39);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_36, 1);
lean_inc(x_50);
lean_dec(x_36);
x_51 = lean_box(0);
x_52 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7(x_3, x_25, x_27, x_4, x_5, x_2, x_29, x_31, x_33, x_35, x_6, x_51, x_8, x_9, x_10, x_11, x_50);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_36);
if (x_53 == 0)
{
return x_36;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_36, 0);
x_55 = lean_ctor_get(x_36, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_36);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term isn’t application of ", 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__3;
x_2 = l_Lean_MessageData_ofName(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__2;
x_2 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__3;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", but of ", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__4;
x_2 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__6;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_7);
x_13 = l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__3;
x_14 = l_Lean_Expr_isConstOf(x_3, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_MessageData_ofExpr(x_3);
x_16 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__7;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_19, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_25, x_8, x_9, x_10, x_11, x_12);
return x_26;
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Value of ", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" is not a lambda application", 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_array_set(x_6, x_7, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_7, x_16);
lean_dec(x_7);
x_5 = x_13;
x_6 = x_15;
x_7 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_7);
x_19 = lean_array_get_size(x_4);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_19);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l_Lean_MessageData_ofName(x_1);
x_23 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__2;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__4;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_26, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(0);
x_33 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9(x_6, x_4, x_5, x_3, x_1, x_2, x_32, x_8, x_9, x_10, x_11, x_12);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_deriveUnaryInduction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_5, x_11);
x_13 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12(x_1, x_2, x_3, x_4, x_5, x_14, x_16, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_deriveUnaryInduction___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_deriveUnaryInduction___lambda__1), 10, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_10);
x_14 = l_Lean_Tactic_FunInd_findFixF___rarg(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_11);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_deriveUnaryInduction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("induct", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_deriveUnaryInduction___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Tactic_FunInd_deriveUnaryInduction___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_deriveUnaryInduction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = l_Lean_Tactic_FunInd_deriveUnaryInduction___closed__2;
lean_inc(x_1);
x_8 = l_Lean_Name_append(x_1, x_7);
lean_inc(x_8);
x_9 = l_Lean_hasConst___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = l_Lean_Tactic_FunInd_deriveUnaryInduction___lambda__2(x_1, x_8, x_13, x_2, x_3, x_4, x_5, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_hasConst___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__6(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__7___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapIdxM_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__7___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mapIdxM_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__9(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; lean_object* x_12; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__4(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_12);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_deriveUnaryInduction___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Tactic_FunInd_deriveUnaryInduction___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = l_Lean_Expr_isAppOf(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__1(x_1, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_13);
x_15 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__1;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
lean_inc(x_1);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_16, x_18);
x_20 = lean_ctor_get(x_2, 3);
lean_inc(x_20);
x_21 = lean_nat_add(x_20, x_17);
lean_dec(x_20);
x_22 = lean_array_get_size(x_19);
x_23 = lean_nat_dec_le(x_21, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_2);
x_24 = lean_box(0);
x_25 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__1(x_1, x_24, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = l_Lean_instInhabitedExpr;
x_27 = l_Array_back___rarg(x_26, x_19);
x_28 = lean_ctor_get(x_2, 4);
lean_inc(x_28);
x_29 = l_Lean_Meta_ArgsPacker_unpack(x_28, x_27, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
lean_dec(x_2);
x_35 = lean_array_get_size(x_34);
x_36 = lean_nat_dec_lt(x_32, x_35);
lean_dec(x_35);
x_37 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
x_38 = l_Lean_Expr_constLevels_x21(x_37);
lean_inc(x_19);
x_39 = lean_array_pop(x_19);
x_40 = lean_array_get_size(x_19);
x_41 = l_Array_toSubarray___rarg(x_19, x_21, x_40);
x_42 = l_Array_ofSubarray___rarg(x_41);
if (x_36 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_34);
lean_dec(x_32);
x_43 = l_Lean_instInhabitedName;
x_44 = l___private_Init_Util_0__outOfBounds___rarg(x_43);
x_45 = l_Lean_Expr_const___override(x_44, x_38);
x_46 = l_Lean_mkAppN(x_45, x_39);
x_47 = l_Lean_mkAppN(x_46, x_33);
x_48 = l_Lean_mkAppN(x_47, x_42);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_29, 0, x_50);
return x_29;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_array_fget(x_34, x_32);
lean_dec(x_32);
lean_dec(x_34);
x_52 = l_Lean_Expr_const___override(x_51, x_38);
x_53 = l_Lean_mkAppN(x_52, x_39);
x_54 = l_Lean_mkAppN(x_53, x_33);
x_55 = l_Lean_mkAppN(x_54, x_42);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_29, 0, x_57);
return x_29;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_58 = lean_ctor_get(x_29, 0);
x_59 = lean_ctor_get(x_29, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_29);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_ctor_get(x_2, 1);
lean_inc(x_62);
lean_dec(x_2);
x_63 = lean_array_get_size(x_62);
x_64 = lean_nat_dec_lt(x_60, x_63);
lean_dec(x_63);
x_65 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
x_66 = l_Lean_Expr_constLevels_x21(x_65);
lean_inc(x_19);
x_67 = lean_array_pop(x_19);
x_68 = lean_array_get_size(x_19);
x_69 = l_Array_toSubarray___rarg(x_19, x_21, x_68);
x_70 = l_Array_ofSubarray___rarg(x_69);
if (x_64 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_62);
lean_dec(x_60);
x_71 = l_Lean_instInhabitedName;
x_72 = l___private_Init_Util_0__outOfBounds___rarg(x_71);
x_73 = l_Lean_Expr_const___override(x_72, x_66);
x_74 = l_Lean_mkAppN(x_73, x_67);
x_75 = l_Lean_mkAppN(x_74, x_61);
x_76 = l_Lean_mkAppN(x_75, x_70);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_59);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_80 = lean_array_fget(x_62, x_60);
lean_dec(x_60);
lean_dec(x_62);
x_81 = l_Lean_Expr_const___override(x_80, x_66);
x_82 = l_Lean_mkAppN(x_81, x_67);
x_83 = l_Lean_mkAppN(x_82, x_61);
x_84 = l_Lean_mkAppN(x_83, x_70);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_59);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_29);
if (x_88 == 0)
{
return x_29;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_29, 0);
x_90 = lean_ctor_get(x_29, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_29);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("PSum", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inr", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__1;
x_2 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__3;
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Expr_isAppOfArity(x_1, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = lean_apply_6(x_2, x_14, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_16 = l_Lean_Expr_appArg_x21(x_1);
x_17 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
x_18 = lean_array_push(x_17, x_16);
x_19 = l_Lean_Expr_beta(x_3, x_18);
x_20 = l_Array_ofSubarray___rarg(x_4);
x_21 = l_Lean_Expr_beta(x_19, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("casesOn", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__1;
x_2 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inl", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__1;
x_2 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__2), 8, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__2;
x_11 = l_Lean_Expr_isAppOf(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__2(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_14);
x_16 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__1;
lean_inc(x_15);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_15, x_18);
lean_dec(x_15);
lean_inc(x_1);
x_20 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_17, x_19);
x_21 = lean_array_get_size(x_20);
x_22 = lean_unsigned_to_nat(6u);
x_23 = lean_nat_dec_le(x_22, x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_9);
x_24 = lean_box(0);
x_25 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__2(x_1, x_2, x_24, x_4, x_5, x_6, x_7, x_8);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_unsigned_to_nat(3u);
x_27 = lean_nat_dec_lt(x_26, x_21);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_dec_lt(x_28, x_21);
x_30 = lean_unsigned_to_nat(5u);
x_31 = lean_nat_dec_lt(x_30, x_21);
lean_dec(x_21);
x_32 = lean_array_get_size(x_20);
lean_inc(x_20);
x_33 = l_Array_toSubarray___rarg(x_20, x_22, x_32);
if (x_27 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Lean_instInhabitedExpr;
x_59 = l___private_Init_Util_0__outOfBounds___rarg(x_58);
x_34 = x_59;
goto block_57;
}
else
{
lean_object* x_60; 
x_60 = lean_array_fget(x_20, x_26);
x_34 = x_60;
goto block_57;
}
block_57:
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_35 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__4;
x_36 = l_Lean_Expr_isAppOfArity(x_34, x_35, x_26);
if (x_29 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Lean_instInhabitedExpr;
x_55 = l___private_Init_Util_0__outOfBounds___rarg(x_54);
x_37 = x_55;
goto block_53;
}
else
{
lean_object* x_56; 
x_56 = lean_array_fget(x_20, x_28);
x_37 = x_56;
goto block_53;
}
block_53:
{
lean_object* x_38; 
if (x_31 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_20);
x_50 = l_Lean_instInhabitedExpr;
x_51 = l___private_Init_Util_0__outOfBounds___rarg(x_50);
x_38 = x_51;
goto block_49;
}
else
{
lean_object* x_52; 
x_52 = lean_array_fget(x_20, x_30);
lean_dec(x_20);
x_38 = x_52;
goto block_49;
}
block_49:
{
if (x_36 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_37);
x_39 = lean_box(0);
x_40 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3(x_34, x_9, x_38, x_33, x_39, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_34);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_38);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_41 = l_Lean_Expr_appArg_x21(x_34);
lean_dec(x_34);
x_42 = l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1;
x_43 = lean_array_push(x_42, x_41);
x_44 = l_Lean_Expr_beta(x_37, x_43);
x_45 = l_Array_ofSubarray___rarg(x_33);
x_46 = l_Lean_Expr_beta(x_44, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_8);
return x_48;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("PSigma", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__1;
x_2 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mk", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__1;
x_2 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Tactic.FunInd.cleanPackedArgs", 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__1;
x_2 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__5;
x_3 = lean_unsigned_to_nat(632u);
x_4 = lean_unsigned_to_nat(50u);
x_5 = l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_3);
x_9 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__2;
x_10 = l_Lean_Expr_isAppOf(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_13);
x_15 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__1;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
lean_inc(x_1);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_16, x_18);
x_20 = lean_array_get_size(x_19);
x_21 = lean_unsigned_to_nat(5u);
x_22 = lean_nat_dec_le(x_21, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4(x_1, x_2, x_23, x_4, x_5, x_6, x_7, x_8);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_unsigned_to_nat(3u);
x_26 = lean_nat_dec_lt(x_25, x_20);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_dec_lt(x_27, x_20);
lean_dec(x_20);
x_29 = lean_array_get_size(x_19);
lean_inc(x_19);
x_30 = l_Array_toSubarray___rarg(x_19, x_21, x_29);
if (x_26 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = l_Lean_instInhabitedExpr;
x_69 = l___private_Init_Util_0__outOfBounds___rarg(x_68);
x_31 = x_69;
goto block_67;
}
else
{
lean_object* x_70; 
x_70 = lean_array_fget(x_19, x_25);
x_31 = x_70;
goto block_67;
}
block_67:
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_32 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__4;
x_33 = l_Lean_Expr_isAppOfArity(x_31, x_32, x_27);
if (x_28 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_19);
x_64 = l_Lean_instInhabitedExpr;
x_65 = l___private_Init_Util_0__outOfBounds___rarg(x_64);
x_34 = x_65;
goto block_63;
}
else
{
lean_object* x_66; 
x_66 = lean_array_fget(x_19, x_27);
lean_dec(x_19);
x_34 = x_66;
goto block_63;
}
block_63:
{
if (x_33 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
x_35 = lean_box(0);
x_36 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4(x_1, x_2, x_35, x_4, x_5, x_6, x_7, x_8);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_31, x_13);
lean_inc(x_37);
x_38 = lean_mk_array(x_37, x_15);
x_39 = lean_nat_sub(x_37, x_17);
lean_dec(x_37);
x_40 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_31, x_38, x_39);
x_41 = lean_array_get_size(x_40);
x_42 = lean_nat_dec_eq(x_41, x_27);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_40);
lean_dec(x_34);
lean_dec(x_30);
x_43 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__6;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_44 = l_panic___at___private_Lean_Meta_WHNF_0__Lean_Meta_cache___spec__1(x_43, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4(x_1, x_2, x_45, x_4, x_5, x_6, x_7, x_46);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_unsigned_to_nat(2u);
x_53 = lean_array_fget(x_40, x_52);
x_54 = lean_array_fget(x_40, x_25);
lean_dec(x_40);
x_55 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__1___closed__1;
x_56 = lean_array_push(x_55, x_53);
x_57 = lean_array_push(x_56, x_54);
x_58 = l_Lean_Expr_beta(x_34, x_57);
x_59 = l_Array_ofSubarray___rarg(x_30);
x_60 = l_Lean_Expr_beta(x_58, x_59);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_8);
return x_62;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_2);
x_8 = l_Lean_Expr_headBeta(x_2);
x_9 = lean_expr_eqv(x_8, x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5(x_2, x_1, x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_cleanPackedArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__7___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__6), 7, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Tactic_FunInd_cleanPackedArgs___closed__1;
x_13 = 0;
x_14 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_9, x_11, x_12, x_13, x_14, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_mkExpectedTypeHint(x_2, x_16, x_3, x_4, x_5, x_6, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
return x_8;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_expr_eqv(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("could not find motive ", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_array_get_size(x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_findIdx_x3f_loop___rarg(x_2, x_9, x_10, x_11, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_13 = l_Lean_MessageData_ofExpr(x_1);
x_14 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__2___closed__2;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__5;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_to_list(lean_box(0), x_2);
x_19 = lean_box(0);
x_20 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_18, x_19);
x_21 = l_Lean_MessageData_ofList(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_LMVarId_getLevel___spec__1(x_24, x_4, x_5, x_6, x_7, x_8);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_ctor_get(x_12, 0);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_8);
return x_27;
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("packed target not last argument to ", 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lean_instInhabitedExpr;
x_15 = l_Array_back___rarg(x_14, x_3);
if (x_13 == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_1);
x_16 = l___private_Init_Util_0__outOfBounds___rarg(x_14);
x_17 = lean_expr_eqv(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_3);
lean_dec(x_2);
x_18 = l_Lean_MessageData_ofName(x_4);
x_19 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_22, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_4);
x_28 = lean_box(0);
x_29 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__2(x_2, x_3, x_28, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_6);
return x_29;
}
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_array_fget(x_1, x_12);
lean_dec(x_1);
x_31 = lean_expr_eqv(x_15, x_30);
lean_dec(x_30);
lean_dec(x_15);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_3);
lean_dec(x_2);
x_32 = l_Lean_MessageData_ofName(x_4);
x_33 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3___closed__2;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_36, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_4);
x_42 = lean_box(0);
x_43 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__2(x_2, x_3, x_42, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_6);
return x_43;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("conclusion ", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" does not look like a packed motive application", 47);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_13; uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_2);
x_25 = l_Lean_Expr_isFVar(x_5);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_26 = lean_box(0);
x_13 = x_26;
goto block_24;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_array_get_size(x_6);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_dec_eq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_box(0);
x_13 = x_30;
goto block_24;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_lt(x_31, x_27);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_27);
lean_dec(x_4);
x_33 = lean_box(0);
x_34 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_33, x_8, x_9, x_10, x_11, x_12);
return x_34;
}
else
{
size_t x_35; size_t x_36; uint8_t x_37; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_37 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__1(x_6, x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_4);
x_38 = lean_box(0);
x_39 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_38, x_8, x_9, x_10, x_11, x_12);
return x_39;
}
else
{
lean_object* x_40; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_40 = lean_box(0);
x_13 = x_40;
goto block_24;
}
}
}
}
block_24:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_13);
x_14 = l_Lean_MessageData_ofExpr(x_4);
x_15 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__2;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__4;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_18, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_8);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
case 1:
{
lean_object* x_41; uint8_t x_53; 
lean_dec(x_7);
lean_dec(x_2);
x_53 = l_Lean_Expr_isFVar(x_5);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_54 = lean_box(0);
x_41 = x_54;
goto block_52;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_array_get_size(x_6);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_dec_eq(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_55);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_58 = lean_box(0);
x_41 = x_58;
goto block_52;
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_nat_dec_lt(x_59, x_55);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_55);
lean_dec(x_4);
x_61 = lean_box(0);
x_62 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_61, x_8, x_9, x_10, x_11, x_12);
return x_62;
}
else
{
size_t x_63; size_t x_64; uint8_t x_65; 
x_63 = 0;
x_64 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_65 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__1(x_6, x_63, x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_4);
x_66 = lean_box(0);
x_67 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_66, x_8, x_9, x_10, x_11, x_12);
return x_67;
}
else
{
lean_object* x_68; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_68 = lean_box(0);
x_41 = x_68;
goto block_52;
}
}
}
}
block_52:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_41);
x_42 = l_Lean_MessageData_ofExpr(x_4);
x_43 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__2;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__4;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_46, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_8);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
case 2:
{
lean_object* x_69; uint8_t x_81; 
lean_dec(x_7);
lean_dec(x_2);
x_81 = l_Lean_Expr_isFVar(x_5);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_82 = lean_box(0);
x_69 = x_82;
goto block_80;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_array_get_size(x_6);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_dec_eq(x_83, x_84);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_83);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_86 = lean_box(0);
x_69 = x_86;
goto block_80;
}
else
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_nat_dec_lt(x_87, x_83);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_83);
lean_dec(x_4);
x_89 = lean_box(0);
x_90 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_89, x_8, x_9, x_10, x_11, x_12);
return x_90;
}
else
{
size_t x_91; size_t x_92; uint8_t x_93; 
x_91 = 0;
x_92 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_93 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__1(x_6, x_91, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_4);
x_94 = lean_box(0);
x_95 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_94, x_8, x_9, x_10, x_11, x_12);
return x_95;
}
else
{
lean_object* x_96; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_96 = lean_box(0);
x_69 = x_96;
goto block_80;
}
}
}
}
block_80:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_69);
x_70 = l_Lean_MessageData_ofExpr(x_4);
x_71 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__2;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__4;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_74, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_8);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
return x_75;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
case 3:
{
lean_object* x_97; uint8_t x_109; 
lean_dec(x_7);
lean_dec(x_2);
x_109 = l_Lean_Expr_isFVar(x_5);
if (x_109 == 0)
{
lean_object* x_110; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_110 = lean_box(0);
x_97 = x_110;
goto block_108;
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_array_get_size(x_6);
x_112 = lean_unsigned_to_nat(1u);
x_113 = lean_nat_dec_eq(x_111, x_112);
if (x_113 == 0)
{
lean_object* x_114; 
lean_dec(x_111);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_114 = lean_box(0);
x_97 = x_114;
goto block_108;
}
else
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_unsigned_to_nat(0u);
x_116 = lean_nat_dec_lt(x_115, x_111);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_111);
lean_dec(x_4);
x_117 = lean_box(0);
x_118 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_117, x_8, x_9, x_10, x_11, x_12);
return x_118;
}
else
{
size_t x_119; size_t x_120; uint8_t x_121; 
x_119 = 0;
x_120 = lean_usize_of_nat(x_111);
lean_dec(x_111);
x_121 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__1(x_6, x_119, x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_4);
x_122 = lean_box(0);
x_123 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_122, x_8, x_9, x_10, x_11, x_12);
return x_123;
}
else
{
lean_object* x_124; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_124 = lean_box(0);
x_97 = x_124;
goto block_108;
}
}
}
}
block_108:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_dec(x_97);
x_98 = l_Lean_MessageData_ofExpr(x_4);
x_99 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__2;
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__4;
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_102, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_8);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
return x_103;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_103, 0);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_103);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
case 4:
{
lean_object* x_125; uint8_t x_137; 
lean_dec(x_7);
lean_dec(x_2);
x_137 = l_Lean_Expr_isFVar(x_5);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_138 = lean_box(0);
x_125 = x_138;
goto block_136;
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_139 = lean_array_get_size(x_6);
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_nat_dec_eq(x_139, x_140);
if (x_141 == 0)
{
lean_object* x_142; 
lean_dec(x_139);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_142 = lean_box(0);
x_125 = x_142;
goto block_136;
}
else
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_unsigned_to_nat(0u);
x_144 = lean_nat_dec_lt(x_143, x_139);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_139);
lean_dec(x_4);
x_145 = lean_box(0);
x_146 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_145, x_8, x_9, x_10, x_11, x_12);
return x_146;
}
else
{
size_t x_147; size_t x_148; uint8_t x_149; 
x_147 = 0;
x_148 = lean_usize_of_nat(x_139);
lean_dec(x_139);
x_149 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__1(x_6, x_147, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_4);
x_150 = lean_box(0);
x_151 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_150, x_8, x_9, x_10, x_11, x_12);
return x_151;
}
else
{
lean_object* x_152; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_152 = lean_box(0);
x_125 = x_152;
goto block_136;
}
}
}
}
block_136:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec(x_125);
x_126 = l_Lean_MessageData_ofExpr(x_4);
x_127 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__2;
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
x_129 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__4;
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_130, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_8);
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
return x_131;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_131, 0);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_131);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
case 5:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_153 = lean_ctor_get(x_5, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_5, 1);
lean_inc(x_154);
lean_dec(x_5);
x_155 = lean_array_set(x_6, x_7, x_154);
x_156 = lean_unsigned_to_nat(1u);
x_157 = lean_nat_sub(x_7, x_156);
lean_dec(x_7);
x_5 = x_153;
x_6 = x_155;
x_7 = x_157;
goto _start;
}
case 6:
{
lean_object* x_159; uint8_t x_171; 
lean_dec(x_7);
lean_dec(x_2);
x_171 = l_Lean_Expr_isFVar(x_5);
if (x_171 == 0)
{
lean_object* x_172; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_172 = lean_box(0);
x_159 = x_172;
goto block_170;
}
else
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_173 = lean_array_get_size(x_6);
x_174 = lean_unsigned_to_nat(1u);
x_175 = lean_nat_dec_eq(x_173, x_174);
if (x_175 == 0)
{
lean_object* x_176; 
lean_dec(x_173);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_176 = lean_box(0);
x_159 = x_176;
goto block_170;
}
else
{
lean_object* x_177; uint8_t x_178; 
x_177 = lean_unsigned_to_nat(0u);
x_178 = lean_nat_dec_lt(x_177, x_173);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_173);
lean_dec(x_4);
x_179 = lean_box(0);
x_180 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_179, x_8, x_9, x_10, x_11, x_12);
return x_180;
}
else
{
size_t x_181; size_t x_182; uint8_t x_183; 
x_181 = 0;
x_182 = lean_usize_of_nat(x_173);
lean_dec(x_173);
x_183 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__1(x_6, x_181, x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_4);
x_184 = lean_box(0);
x_185 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_184, x_8, x_9, x_10, x_11, x_12);
return x_185;
}
else
{
lean_object* x_186; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_186 = lean_box(0);
x_159 = x_186;
goto block_170;
}
}
}
}
block_170:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
lean_dec(x_159);
x_160 = l_Lean_MessageData_ofExpr(x_4);
x_161 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__2;
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__4;
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_164, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_8);
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
return x_165;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_165, 0);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_165);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
case 7:
{
lean_object* x_187; uint8_t x_199; 
lean_dec(x_7);
lean_dec(x_2);
x_199 = l_Lean_Expr_isFVar(x_5);
if (x_199 == 0)
{
lean_object* x_200; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_200 = lean_box(0);
x_187 = x_200;
goto block_198;
}
else
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_201 = lean_array_get_size(x_6);
x_202 = lean_unsigned_to_nat(1u);
x_203 = lean_nat_dec_eq(x_201, x_202);
if (x_203 == 0)
{
lean_object* x_204; 
lean_dec(x_201);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_204 = lean_box(0);
x_187 = x_204;
goto block_198;
}
else
{
lean_object* x_205; uint8_t x_206; 
x_205 = lean_unsigned_to_nat(0u);
x_206 = lean_nat_dec_lt(x_205, x_201);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; 
lean_dec(x_201);
lean_dec(x_4);
x_207 = lean_box(0);
x_208 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_207, x_8, x_9, x_10, x_11, x_12);
return x_208;
}
else
{
size_t x_209; size_t x_210; uint8_t x_211; 
x_209 = 0;
x_210 = lean_usize_of_nat(x_201);
lean_dec(x_201);
x_211 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__1(x_6, x_209, x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; 
lean_dec(x_4);
x_212 = lean_box(0);
x_213 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_212, x_8, x_9, x_10, x_11, x_12);
return x_213;
}
else
{
lean_object* x_214; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_214 = lean_box(0);
x_187 = x_214;
goto block_198;
}
}
}
}
block_198:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
lean_dec(x_187);
x_188 = l_Lean_MessageData_ofExpr(x_4);
x_189 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__2;
x_190 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
x_191 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__4;
x_192 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_192, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_8);
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
return x_193;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_193, 0);
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_193);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
case 8:
{
lean_object* x_215; uint8_t x_227; 
lean_dec(x_7);
lean_dec(x_2);
x_227 = l_Lean_Expr_isFVar(x_5);
if (x_227 == 0)
{
lean_object* x_228; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_228 = lean_box(0);
x_215 = x_228;
goto block_226;
}
else
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_229 = lean_array_get_size(x_6);
x_230 = lean_unsigned_to_nat(1u);
x_231 = lean_nat_dec_eq(x_229, x_230);
if (x_231 == 0)
{
lean_object* x_232; 
lean_dec(x_229);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_232 = lean_box(0);
x_215 = x_232;
goto block_226;
}
else
{
lean_object* x_233; uint8_t x_234; 
x_233 = lean_unsigned_to_nat(0u);
x_234 = lean_nat_dec_lt(x_233, x_229);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; 
lean_dec(x_229);
lean_dec(x_4);
x_235 = lean_box(0);
x_236 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_235, x_8, x_9, x_10, x_11, x_12);
return x_236;
}
else
{
size_t x_237; size_t x_238; uint8_t x_239; 
x_237 = 0;
x_238 = lean_usize_of_nat(x_229);
lean_dec(x_229);
x_239 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__1(x_6, x_237, x_238);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_4);
x_240 = lean_box(0);
x_241 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_240, x_8, x_9, x_10, x_11, x_12);
return x_241;
}
else
{
lean_object* x_242; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_242 = lean_box(0);
x_215 = x_242;
goto block_226;
}
}
}
}
block_226:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
lean_dec(x_215);
x_216 = l_Lean_MessageData_ofExpr(x_4);
x_217 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__2;
x_218 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_216);
x_219 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__4;
x_220 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_220, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_8);
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
return x_221;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_221, 0);
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_221);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
case 9:
{
lean_object* x_243; uint8_t x_255; 
lean_dec(x_7);
lean_dec(x_2);
x_255 = l_Lean_Expr_isFVar(x_5);
if (x_255 == 0)
{
lean_object* x_256; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_256 = lean_box(0);
x_243 = x_256;
goto block_254;
}
else
{
lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_257 = lean_array_get_size(x_6);
x_258 = lean_unsigned_to_nat(1u);
x_259 = lean_nat_dec_eq(x_257, x_258);
if (x_259 == 0)
{
lean_object* x_260; 
lean_dec(x_257);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_260 = lean_box(0);
x_243 = x_260;
goto block_254;
}
else
{
lean_object* x_261; uint8_t x_262; 
x_261 = lean_unsigned_to_nat(0u);
x_262 = lean_nat_dec_lt(x_261, x_257);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_257);
lean_dec(x_4);
x_263 = lean_box(0);
x_264 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_263, x_8, x_9, x_10, x_11, x_12);
return x_264;
}
else
{
size_t x_265; size_t x_266; uint8_t x_267; 
x_265 = 0;
x_266 = lean_usize_of_nat(x_257);
lean_dec(x_257);
x_267 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__1(x_6, x_265, x_266);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; 
lean_dec(x_4);
x_268 = lean_box(0);
x_269 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_268, x_8, x_9, x_10, x_11, x_12);
return x_269;
}
else
{
lean_object* x_270; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_270 = lean_box(0);
x_243 = x_270;
goto block_254;
}
}
}
}
block_254:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
lean_dec(x_243);
x_244 = l_Lean_MessageData_ofExpr(x_4);
x_245 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__2;
x_246 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_244);
x_247 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__4;
x_248 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
x_249 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_248, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_8);
x_250 = !lean_is_exclusive(x_249);
if (x_250 == 0)
{
return x_249;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_249, 0);
x_252 = lean_ctor_get(x_249, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_249);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
case 10:
{
lean_object* x_271; uint8_t x_283; 
lean_dec(x_7);
lean_dec(x_2);
x_283 = l_Lean_Expr_isFVar(x_5);
if (x_283 == 0)
{
lean_object* x_284; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_284 = lean_box(0);
x_271 = x_284;
goto block_282;
}
else
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_285 = lean_array_get_size(x_6);
x_286 = lean_unsigned_to_nat(1u);
x_287 = lean_nat_dec_eq(x_285, x_286);
if (x_287 == 0)
{
lean_object* x_288; 
lean_dec(x_285);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_288 = lean_box(0);
x_271 = x_288;
goto block_282;
}
else
{
lean_object* x_289; uint8_t x_290; 
x_289 = lean_unsigned_to_nat(0u);
x_290 = lean_nat_dec_lt(x_289, x_285);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; 
lean_dec(x_285);
lean_dec(x_4);
x_291 = lean_box(0);
x_292 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_291, x_8, x_9, x_10, x_11, x_12);
return x_292;
}
else
{
size_t x_293; size_t x_294; uint8_t x_295; 
x_293 = 0;
x_294 = lean_usize_of_nat(x_285);
lean_dec(x_285);
x_295 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__1(x_6, x_293, x_294);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; 
lean_dec(x_4);
x_296 = lean_box(0);
x_297 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_296, x_8, x_9, x_10, x_11, x_12);
return x_297;
}
else
{
lean_object* x_298; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_298 = lean_box(0);
x_271 = x_298;
goto block_282;
}
}
}
}
block_282:
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
lean_dec(x_271);
x_272 = l_Lean_MessageData_ofExpr(x_4);
x_273 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__2;
x_274 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_272);
x_275 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__4;
x_276 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
x_277 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_276, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_8);
x_278 = !lean_is_exclusive(x_277);
if (x_278 == 0)
{
return x_277;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_277, 0);
x_280 = lean_ctor_get(x_277, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_277);
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
return x_281;
}
}
}
default: 
{
lean_object* x_299; uint8_t x_311; 
lean_dec(x_7);
lean_dec(x_2);
x_311 = l_Lean_Expr_isFVar(x_5);
if (x_311 == 0)
{
lean_object* x_312; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_312 = lean_box(0);
x_299 = x_312;
goto block_310;
}
else
{
lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_313 = lean_array_get_size(x_6);
x_314 = lean_unsigned_to_nat(1u);
x_315 = lean_nat_dec_eq(x_313, x_314);
if (x_315 == 0)
{
lean_object* x_316; 
lean_dec(x_313);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_316 = lean_box(0);
x_299 = x_316;
goto block_310;
}
else
{
lean_object* x_317; uint8_t x_318; 
x_317 = lean_unsigned_to_nat(0u);
x_318 = lean_nat_dec_lt(x_317, x_313);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; 
lean_dec(x_313);
lean_dec(x_4);
x_319 = lean_box(0);
x_320 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_319, x_8, x_9, x_10, x_11, x_12);
return x_320;
}
else
{
size_t x_321; size_t x_322; uint8_t x_323; 
x_321 = 0;
x_322 = lean_usize_of_nat(x_313);
lean_dec(x_313);
x_323 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__1(x_6, x_321, x_322);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; 
lean_dec(x_4);
x_324 = lean_box(0);
x_325 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_6, x_5, x_3, x_1, x_324, x_8, x_9, x_10, x_11, x_12);
return x_325;
}
else
{
lean_object* x_326; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_326 = lean_box(0);
x_299 = x_326;
goto block_310;
}
}
}
}
block_310:
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
lean_dec(x_299);
x_300 = l_Lean_MessageData_ofExpr(x_4);
x_301 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__2;
x_302 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_300);
x_303 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__4;
x_304 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
x_305 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_304, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_8);
x_306 = !lean_is_exclusive(x_305);
if (x_306 == 0)
{
return x_305;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_305, 0);
x_308 = lean_ctor_get(x_305, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_305);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_4, x_10);
x_12 = l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__1;
lean_inc(x_11);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_11, x_14);
lean_dec(x_11);
lean_inc(x_4);
x_16 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1(x_1, x_2, x_3, x_4, x_4, x_13, x_15, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_pop(x_6);
lean_inc(x_13);
x_14 = l_Lean_mkAppN(x_1, x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_15 = l_Lean_Meta_ArgsPacker_curry(x_2, x_14, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 0;
x_19 = 1;
x_20 = 1;
x_21 = l_Lean_Meta_mkLambdaFVars(x_13, x_16, x_18, x_19, x_20, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_mkLambdaFVars(x_3, x_22, x_18, x_19, x_20, x_8, x_9, x_10, x_11, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_mkLambdaFVars(x_4, x_25, x_18, x_19, x_20, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_28);
x_30 = l_Lean_Meta_check(x_28, x_8, x_9, x_10, x_11, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Tactic_FunInd_cleanPackedArgs(x_5, x_28, x_8, x_9, x_10, x_11, x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_30);
if (x_41 == 0)
{
return x_30;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_30, 0);
x_43 = lean_ctor_get(x_30, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_30);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_27);
if (x_45 == 0)
{
return x_27;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_27, 0);
x_47 = lean_ctor_get(x_27, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_27);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_24);
if (x_49 == 0)
{
return x_24;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_24, 0);
x_51 = lean_ctor_get(x_24, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_24);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_21);
if (x_53 == 0)
{
return x_21;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_21, 0);
x_55 = lean_ctor_get(x_21, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_21);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_15);
if (x_57 == 0)
{
return x_15;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_15, 0);
x_59 = lean_ctor_get(x_15, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_15);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__2___boxed), 12, 5);
lean_closure_set(x_12, 0, x_5);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_2);
lean_closure_set(x_12, 4, x_3);
x_13 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_6, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_3);
x_10 = l_Lean_mkAppN(x_1, x_3);
x_11 = lean_ctor_get(x_2, 4);
lean_inc(x_11);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__3), 11, 3);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_2);
x_13 = l_Lean_Meta_ArgsPacker_curryParam___rarg(x_11, x_10, x_4, x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_11 = lean_infer_type(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__2;
x_15 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__3;
lean_inc(x_9);
lean_inc(x_8);
x_16 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_12, x_14, x_15, x_8, x_9, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_2);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_19, 2, x_17);
lean_inc(x_2);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_4);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_1);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_addDecl(x_22, x_8, x_9, x_18);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_2);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
return x_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
return x_11;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_11, 0);
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_11);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instMonadExceptOfExceptionCoreM;
x_2 = l_StateRefT_x27_instMonadExceptOfStateRefT_x27___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__1;
x_2 = l_ReaderT_instMonadExceptOfReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadFunctorReaderT), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLiftReaderT), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_lift), 4, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__3;
x_2 = l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__5;
x_3 = l_Lean_Core_instMonadQuotationCoreM;
x_4 = l_Lean_instMonadQuotation___rarg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__3;
x_2 = l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__4;
x_3 = l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__6;
x_4 = l_Lean_instMonadQuotation___rarg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instAddMessageContextMetaM;
x_2 = l_Lean_Meta_instMonadMetaM;
x_3 = lean_alloc_closure((void*)(l_Lean_instAddErrorMessageContext___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__7;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__2;
x_4 = l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__8;
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to unpack induction priciple:", 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_dec(x_4);
lean_inc(x_1);
x_10 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_ConstantInfo_levelParams(x_11);
x_14 = l_Lean_ConstantInfo_name(x_11);
x_15 = lean_box(0);
lean_inc(x_13);
x_16 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_13, x_15);
x_17 = l_Lean_Expr_const___override(x_14, x_16);
x_18 = l_Lean_ConstantInfo_type(x_11);
lean_dec(x_11);
x_19 = l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__9;
x_20 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__1), 9, 2);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_18);
x_21 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_18, x_20, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__4), 9, 2);
lean_closure_set(x_25, 0, x_17);
lean_closure_set(x_25, 1, x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_26 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__5___rarg(x_18, x_24, x_25, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_27);
x_29 = l_Lean_Meta_isTypeCorrect(x_27, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
lean_inc(x_27);
x_33 = l_Lean_indentExpr(x_27);
x_34 = l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__11;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = 2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_39 = l_Lean_log___at_Lean_Meta_computeSynthOrder___spec__6(x_37, x_38, x_5, x_6, x_7, x_8, x_32);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_27);
x_41 = l_Lean_Meta_check(x_27, x_5, x_6, x_7, x_8, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__5(x_27, x_3, x_13, x_15, x_42, x_5, x_6, x_7, x_8, x_43);
lean_dec(x_42);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_29, 1);
lean_inc(x_49);
lean_dec(x_29);
x_50 = lean_box(0);
x_51 = l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__5(x_27, x_3, x_13, x_15, x_50, x_5, x_6, x_7, x_8, x_49);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_29);
if (x_52 == 0)
{
return x_29;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_29, 0);
x_54 = lean_ctor_get(x_29, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_29);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_26);
if (x_56 == 0)
{
return x_26;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_26, 0);
x_58 = lean_ctor_get(x_26, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_26);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_21);
if (x_60 == 0)
{
return x_21;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_21, 0);
x_62 = lean_ctor_get(x_21, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_21);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_10);
if (x_64 == 0)
{
return x_10;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_10, 0);
x_66 = lean_ctor_get(x_10, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_10);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_unpackMutualInduction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mutual_induct", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_unpackMutualInduction___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Tactic_FunInd_unpackMutualInduction___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_array_get_size(x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_dec_lt(x_22, x_21);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_lt(x_24, x_21);
lean_dec(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_20);
x_26 = l_Lean_instInhabitedName;
x_27 = l___private_Init_Util_0__outOfBounds___rarg(x_26);
x_28 = l_Lean_Tactic_FunInd_deriveUnaryInduction___closed__2;
x_29 = l_Lean_Name_append(x_27, x_28);
x_8 = x_29;
goto block_19;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_array_fget(x_20, x_24);
lean_dec(x_20);
x_31 = l_Lean_Tactic_FunInd_deriveUnaryInduction___closed__2;
x_32 = l_Lean_Name_append(x_30, x_31);
x_8 = x_32;
goto block_19;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_lt(x_33, x_21);
lean_dec(x_21);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_20);
x_35 = l_Lean_instInhabitedName;
x_36 = l___private_Init_Util_0__outOfBounds___rarg(x_35);
x_37 = l_Lean_Tactic_FunInd_unpackMutualInduction___closed__2;
x_38 = l_Lean_Name_append(x_36, x_37);
x_8 = x_38;
goto block_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_array_fget(x_20, x_33);
lean_dec(x_20);
x_40 = l_Lean_Tactic_FunInd_unpackMutualInduction___closed__2;
x_41 = l_Lean_Name_append(x_39, x_40);
x_8 = x_41;
goto block_19;
}
}
block_19:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_8);
x_9 = l_Lean_hasConst___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__1(x_8, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6(x_2, x_1, x_8, x_13, x_3, x_4, x_5, x_6, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deriveUnpackedInduction___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_12 = l_Lean_ConstantInfo_name(x_1);
x_13 = lean_box(0);
x_14 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_2, x_13);
x_15 = l_Lean_Expr_const___override(x_12, x_14);
lean_inc(x_5);
x_16 = l_Lean_mkAppN(x_15, x_5);
x_17 = l_Lean_Meta_mkProjAndN(x_3, x_4, x_16);
x_18 = 0;
x_19 = 1;
x_20 = 1;
x_21 = l_Lean_Meta_mkLambdaFVars(x_5, x_17, x_18, x_19, x_20, x_7, x_8, x_9, x_10, x_11);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deriveUnpackedInduction___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_15 = lean_array_uget(x_4, x_6);
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 2);
lean_inc(x_27);
x_28 = lean_nat_dec_lt(x_25, x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_15);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_7);
x_16 = x_29;
x_17 = x_12;
goto block_24;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_31 = lean_ctor_get(x_7, 2);
lean_dec(x_31);
x_32 = lean_ctor_get(x_7, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_7, 0);
lean_dec(x_33);
x_34 = lean_nat_add(x_25, x_27);
lean_ctor_set(x_7, 0, x_34);
x_35 = l_Lean_Tactic_FunInd_deriveUnaryInduction___closed__2;
x_36 = l_Lean_Name_append(x_15, x_35);
lean_inc(x_36);
x_37 = l_Lean_hasConst___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__1(x_36, x_8, x_9, x_10, x_11, x_12);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l_Lean_ConstantInfo_type(x_1);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_42 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deriveUnpackedInduction___spec__1___lambda__1___boxed), 11, 4);
lean_closure_set(x_42, 0, x_1);
lean_closure_set(x_42, 1, x_2);
lean_closure_set(x_42, 2, x_3);
lean_closure_set(x_42, 3, x_25);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_43 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_41, x_42, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_44);
x_46 = lean_infer_type(x_44, x_8, x_9, x_10, x_11, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_2);
lean_inc(x_36);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_36);
lean_ctor_set(x_49, 1, x_2);
lean_ctor_set(x_49, 2, x_47);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_36);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_44);
lean_ctor_set(x_52, 2, x_51);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_inc(x_11);
lean_inc(x_10);
x_54 = l_Lean_addDecl(x_53, x_10, x_11, x_48);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_7);
x_16 = x_56;
x_17 = x_55;
goto block_24;
}
else
{
uint8_t x_57; 
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_54, 0);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_54);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_44);
lean_dec(x_36);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_46);
if (x_61 == 0)
{
return x_46;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_46, 0);
x_63 = lean_ctor_get(x_46, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_46);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_36);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_43);
if (x_65 == 0)
{
return x_43;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_43, 0);
x_67 = lean_ctor_get(x_43, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_43);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_36);
lean_dec(x_25);
x_69 = lean_ctor_get(x_37, 1);
lean_inc(x_69);
lean_dec(x_37);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_7);
x_16 = x_70;
x_17 = x_69;
goto block_24;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_7);
x_71 = lean_nat_add(x_25, x_27);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_26);
lean_ctor_set(x_72, 2, x_27);
x_73 = l_Lean_Tactic_FunInd_deriveUnaryInduction___closed__2;
x_74 = l_Lean_Name_append(x_15, x_73);
lean_inc(x_74);
x_75 = l_Lean_hasConst___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__1(x_74, x_8, x_9, x_10, x_11, x_12);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = l_Lean_ConstantInfo_type(x_1);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_80 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deriveUnpackedInduction___spec__1___lambda__1___boxed), 11, 4);
lean_closure_set(x_80, 0, x_1);
lean_closure_set(x_80, 1, x_2);
lean_closure_set(x_80, 2, x_3);
lean_closure_set(x_80, 3, x_25);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_81 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_79, x_80, x_8, x_9, x_10, x_11, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_82);
x_84 = lean_infer_type(x_82, x_8, x_9, x_10, x_11, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_2);
lean_inc(x_74);
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_74);
lean_ctor_set(x_87, 1, x_2);
lean_ctor_set(x_87, 2, x_85);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_74);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_82);
lean_ctor_set(x_90, 2, x_89);
x_91 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_91, 0, x_90);
lean_inc(x_11);
lean_inc(x_10);
x_92 = l_Lean_addDecl(x_91, x_10, x_11, x_86);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_72);
x_16 = x_94;
x_17 = x_93;
goto block_24;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_72);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_97 = x_92;
} else {
 lean_dec_ref(x_92);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = lean_ctor_get(x_84, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_84, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_101 = x_84;
} else {
 lean_dec_ref(x_84);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = lean_ctor_get(x_81, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_81, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_105 = x_81;
} else {
 lean_dec_ref(x_81);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_74);
lean_dec(x_25);
x_107 = lean_ctor_get(x_75, 1);
lean_inc(x_107);
lean_dec(x_75);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_72);
x_16 = x_108;
x_17 = x_107;
goto block_24;
}
}
}
block_24:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = 1;
x_22 = lean_usize_add(x_6, x_21);
x_6 = x_22;
x_7 = x_20;
x_12 = x_17;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_deriveUnpackedInduction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Tactic_FunInd_unpackMutualInduction(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_ConstantInfo_levelParams(x_12);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_unsigned_to_nat(1u);
lean_inc(x_16);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_get_size(x_15);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = 0;
x_23 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deriveUnpackedInduction___spec__1(x_12, x_14, x_16, x_15, x_21, x_22, x_19, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_15);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_11);
if (x_34 == 0)
{
return x_11;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_11, 0);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_11);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_8);
if (x_38 == 0)
{
return x_8;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_8, 0);
x_40 = lean_ctor_get(x_8, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_8);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deriveUnpackedInduction___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deriveUnpackedInduction___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deriveUnpackedInduction___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_deriveUnpackedInduction___spec__1(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_15;
}
}
static lean_object* _init_l_Lean_Tactic_FunInd_deriveInduction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_WF_eqnInfoExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_deriveInduction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_WF_instInhabitedEqnInfo;
x_12 = l_Lean_Tactic_FunInd_deriveInduction___closed__1;
lean_inc(x_1);
x_13 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_11, x_12, x_10, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Tactic_FunInd_deriveUnaryInduction(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_ctor_get(x_25, 2);
lean_inc(x_26);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_26);
x_27 = l_Lean_Tactic_FunInd_deriveUnaryInduction(x_26, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_name_eq(x_26, x_1);
lean_dec(x_1);
lean_dec(x_26);
if (x_31 == 0)
{
lean_object* x_32; 
lean_free_object(x_27);
x_32 = l_Lean_Tactic_FunInd_deriveUnpackedInduction(x_25, x_29, x_2, x_3, x_4, x_5, x_30);
return x_32;
}
else
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_box(0);
lean_ctor_set(x_27, 0, x_33);
return x_27;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_name_eq(x_26, x_1);
lean_dec(x_1);
lean_dec(x_26);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Lean_Tactic_FunInd_deriveUnpackedInduction(x_25, x_34, x_2, x_3, x_4, x_5, x_35);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_34);
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_27);
if (x_40 == 0)
{
return x_27;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_27, 0);
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_27);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_elabDeriveInduction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_11, x_12, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Tactic_FunInd_deriveInduction(x_14, x_5, x_6, x_7, x_8, x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_elabDeriveInduction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_elabDeriveInduction___lambda__1___boxed), 9, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_Command_runTermElabM___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_elabDeriveInduction___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Tactic_FunInd_elabDeriveInduction___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Tactic_FunInd_elabDeriveInduction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Tactic_FunInd_elabDeriveInduction(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("deriveInduction", 15);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__1;
x_2 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__2;
x_3 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__3;
x_4 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("FunInd", 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabDeriveInduction", 19);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__1;
x_2 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__6;
x_3 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__7;
x_4 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Tactic_FunInd_elabDeriveInduction___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__10;
x_3 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__5;
x_4 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__9;
x_5 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__11;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(742u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(745u);
x_2 = lean_unsigned_to_nat(22u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__2;
x_4 = lean_unsigned_to_nat(22u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(742u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(742u);
x_2 = lean_unsigned_to_nat(23u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__5;
x_4 = lean_unsigned_to_nat(23u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__9;
x_3 = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherApp_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Cleanup(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Injective(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_ArgsPacker(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_FunInd(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherApp_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cleanup(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Injective(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ArgsPacker(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Tactic_FunInd_removeLamda___rarg___closed__1 = _init_l_Lean_Tactic_FunInd_removeLamda___rarg___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_removeLamda___rarg___closed__1);
l_Lean_Tactic_FunInd_removeLamda___rarg___closed__2 = _init_l_Lean_Tactic_FunInd_removeLamda___rarg___closed__2();
lean_mark_persistent(l_Lean_Tactic_FunInd_removeLamda___rarg___closed__2);
l_Lean_Tactic_FunInd_removeLamda___rarg___closed__3 = _init_l_Lean_Tactic_FunInd_removeLamda___rarg___closed__3();
lean_mark_persistent(l_Lean_Tactic_FunInd_removeLamda___rarg___closed__3);
l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4 = _init_l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4();
lean_mark_persistent(l_Lean_Tactic_FunInd_removeLamda___rarg___closed__4);
l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1 = _init_l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_foldCalls___lambda__1___closed__1);
l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__1 = _init_l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__1);
l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__2 = _init_l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__2);
l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__3 = _init_l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__3);
l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__4 = _init_l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__4);
l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__5 = _init_l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__5);
l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__6 = _init_l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Tactic_FunInd_foldCalls___lambda__3___closed__6);
l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__1 = _init_l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__1);
l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__2 = _init_l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__2();
lean_mark_persistent(l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__2);
l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__3 = _init_l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__3();
lean_mark_persistent(l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__3);
l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__4 = _init_l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__4();
lean_mark_persistent(l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__4);
l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__5 = _init_l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__5();
lean_mark_persistent(l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__5);
l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__6 = _init_l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__6();
lean_mark_persistent(l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__6);
l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__7 = _init_l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__7();
lean_mark_persistent(l_Lean_Tactic_FunInd_foldCalls___lambda__7___closed__7);
l_Lean_Tactic_FunInd_foldCalls___lambda__8___closed__1 = _init_l_Lean_Tactic_FunInd_foldCalls___lambda__8___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_foldCalls___lambda__8___closed__1);
l_Lean_Tactic_FunInd_foldCalls___lambda__8___closed__2 = _init_l_Lean_Tactic_FunInd_foldCalls___lambda__8___closed__2();
lean_mark_persistent(l_Lean_Tactic_FunInd_foldCalls___lambda__8___closed__2);
l_Lean_Tactic_FunInd_foldCalls___lambda__10___closed__1 = _init_l_Lean_Tactic_FunInd_foldCalls___lambda__10___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_foldCalls___lambda__10___closed__1);
l_Lean_Tactic_FunInd_foldCalls___lambda__11___closed__1 = _init_l_Lean_Tactic_FunInd_foldCalls___lambda__11___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_foldCalls___lambda__11___closed__1);
l_Lean_Tactic_FunInd_foldCalls___lambda__12___closed__1 = _init_l_Lean_Tactic_FunInd_foldCalls___lambda__12___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_foldCalls___lambda__12___closed__1);
l_panic___at_Lean_Tactic_FunInd_collectIHs___spec__1___closed__1 = _init_l_panic___at_Lean_Tactic_FunInd_collectIHs___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Tactic_FunInd_collectIHs___spec__1___closed__1);
l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__1 = _init_l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__1);
l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__2 = _init_l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__2);
l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__3 = _init_l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__3);
l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__4 = _init_l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Tactic_FunInd_collectIHs___lambda__4___closed__4);
l_Lean_Tactic_FunInd_collectIHs___lambda__5___closed__1 = _init_l_Lean_Tactic_FunInd_collectIHs___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_collectIHs___lambda__5___closed__1);
l_Lean_Tactic_FunInd_collectIHs___lambda__5___closed__2 = _init_l_Lean_Tactic_FunInd_collectIHs___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Tactic_FunInd_collectIHs___lambda__5___closed__2);
l_Lean_Tactic_FunInd_collectIHs___lambda__7___closed__1 = _init_l_Lean_Tactic_FunInd_collectIHs___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_collectIHs___lambda__7___closed__1);
l_Lean_Tactic_FunInd_collectIHs___lambda__7___closed__2 = _init_l_Lean_Tactic_FunInd_collectIHs___lambda__7___closed__2();
lean_mark_persistent(l_Lean_Tactic_FunInd_collectIHs___lambda__7___closed__2);
l_Lean_Tactic_FunInd_collectIHs___lambda__8___closed__1 = _init_l_Lean_Tactic_FunInd_collectIHs___lambda__8___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_collectIHs___lambda__8___closed__1);
l_Lean_Tactic_FunInd_collectIHs___lambda__8___closed__2 = _init_l_Lean_Tactic_FunInd_collectIHs___lambda__8___closed__2();
lean_mark_persistent(l_Lean_Tactic_FunInd_collectIHs___lambda__8___closed__2);
l_Lean_Tactic_FunInd_collectIHs___lambda__8___closed__3 = _init_l_Lean_Tactic_FunInd_collectIHs___lambda__8___closed__3();
lean_mark_persistent(l_Lean_Tactic_FunInd_collectIHs___lambda__8___closed__3);
l_Lean_Tactic_FunInd_collectIHs___lambda__9___closed__1 = _init_l_Lean_Tactic_FunInd_collectIHs___lambda__9___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_collectIHs___lambda__9___closed__1);
l_Lean_Tactic_FunInd_collectIHs___lambda__10___closed__1 = _init_l_Lean_Tactic_FunInd_collectIHs___lambda__10___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_collectIHs___lambda__10___closed__1);
l_Lean_Tactic_FunInd_collectIHs___lambda__16___closed__1 = _init_l_Lean_Tactic_FunInd_collectIHs___lambda__16___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_collectIHs___lambda__16___closed__1);
l_Lean_Tactic_FunInd_deduplicateIHs___closed__1 = _init_l_Lean_Tactic_FunInd_deduplicateIHs___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_deduplicateIHs___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_assertIHs___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_assertIHs___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Tactic_FunInd_assertIHs___spec__1___closed__1);
l_Lean_Tactic_FunInd_buildInductionCase___closed__1 = _init_l_Lean_Tactic_FunInd_buildInductionCase___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_buildInductionCase___closed__1);
l_Lean_Tactic_FunInd_buildInductionCase___closed__2 = _init_l_Lean_Tactic_FunInd_buildInductionCase___closed__2();
lean_mark_persistent(l_Lean_Tactic_FunInd_buildInductionCase___closed__2);
l_Lean_Loop_forIn_loop___at_Lean_Tactic_FunInd_mkLambdaFVarsMasked___spec__1___closed__1 = _init_l_Lean_Loop_forIn_loop___at_Lean_Tactic_FunInd_mkLambdaFVarsMasked___spec__1___closed__1();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Tactic_FunInd_mkLambdaFVarsMasked___spec__1___closed__1);
l_Lean_Tactic_FunInd_buildInductionBody___lambda__7___closed__1 = _init_l_Lean_Tactic_FunInd_buildInductionBody___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_buildInductionBody___lambda__7___closed__1);
l_Lean_Tactic_FunInd_buildInductionBody___lambda__7___closed__2 = _init_l_Lean_Tactic_FunInd_buildInductionBody___lambda__7___closed__2();
lean_mark_persistent(l_Lean_Tactic_FunInd_buildInductionBody___lambda__7___closed__2);
l_Lean_Tactic_FunInd_buildInductionBody___lambda__11___closed__1 = _init_l_Lean_Tactic_FunInd_buildInductionBody___lambda__11___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_buildInductionBody___lambda__11___closed__1);
l_Lean_Tactic_FunInd_buildInductionBody___closed__1 = _init_l_Lean_Tactic_FunInd_buildInductionBody___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_buildInductionBody___closed__1);
l_Lean_Tactic_FunInd_buildInductionBody___closed__2 = _init_l_Lean_Tactic_FunInd_buildInductionBody___closed__2();
lean_mark_persistent(l_Lean_Tactic_FunInd_buildInductionBody___closed__2);
l_Lean_Tactic_FunInd_buildInductionBody___closed__3 = _init_l_Lean_Tactic_FunInd_buildInductionBody___closed__3();
lean_mark_persistent(l_Lean_Tactic_FunInd_buildInductionBody___closed__3);
l_Lean_Tactic_FunInd_buildInductionBody___closed__4 = _init_l_Lean_Tactic_FunInd_buildInductionBody___closed__4();
lean_mark_persistent(l_Lean_Tactic_FunInd_buildInductionBody___closed__4);
l_Lean_Tactic_FunInd_buildInductionBody___closed__5 = _init_l_Lean_Tactic_FunInd_buildInductionBody___closed__5();
lean_mark_persistent(l_Lean_Tactic_FunInd_buildInductionBody___closed__5);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__1 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__1);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__2 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__2);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__3 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__3);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__4 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__4);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__5 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__5);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__6 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__6);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__7 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__7);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__8 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__8);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__9 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__9);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__10 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__10();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__10);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__11 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__11();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__11);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__12 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__12();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__12);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__13 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__13();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__13);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__14 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__14();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__14);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__15 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__15();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__15);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__16 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__16();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__16);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__17 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__17();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__17);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__18 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__18();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__18);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__19 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__19();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__19);
l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__20 = _init_l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__20();
lean_mark_persistent(l_Lean_Tactic_FunInd_findFixF___rarg___lambda__2___closed__20);
l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__1 = _init_l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__1();
lean_mark_persistent(l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__1);
l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__2 = _init_l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__2();
lean_mark_persistent(l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__2);
l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__3 = _init_l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__3();
lean_mark_persistent(l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__3);
l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__4 = _init_l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__4();
lean_mark_persistent(l_Lean_getConstInfoDefn___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__2___closed__4);
l_Array_mapIdxM_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__7___closed__1 = _init_l_Array_mapIdxM_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__7___closed__1();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__7___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__1___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__1___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__4 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__2___closed__4);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__3___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__3___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__3___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__3___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__4 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__4);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__5 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___closed__5);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___boxed__const__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__6___boxed__const__1);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__7___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__4 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__4);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__5 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__5);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__6 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__6();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__8___closed__6);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__4 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__4);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__5 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__5);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__6 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__6();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__6);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__7 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__7();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___lambda__9___closed__7);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__4 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_deriveUnaryInduction___spec__12___closed__4);
l_Lean_Tactic_FunInd_deriveUnaryInduction___closed__1 = _init_l_Lean_Tactic_FunInd_deriveUnaryInduction___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_deriveUnaryInduction___closed__1);
l_Lean_Tactic_FunInd_deriveUnaryInduction___closed__2 = _init_l_Lean_Tactic_FunInd_deriveUnaryInduction___closed__2();
lean_mark_persistent(l_Lean_Tactic_FunInd_deriveUnaryInduction___closed__2);
l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__1 = _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__1);
l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__2 = _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__2);
l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__3 = _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__3___closed__3);
l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__1 = _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__1);
l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__2 = _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__2);
l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__3 = _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__3);
l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__4 = _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__4___closed__4);
l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__1 = _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__1);
l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__2 = _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__2);
l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__3 = _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__3);
l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__4 = _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__4();
lean_mark_persistent(l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__4);
l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__5 = _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__5();
lean_mark_persistent(l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__5);
l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__6 = _init_l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__6();
lean_mark_persistent(l_Lean_Tactic_FunInd_cleanPackedArgs___lambda__5___closed__6);
l_Lean_Tactic_FunInd_cleanPackedArgs___closed__1 = _init_l_Lean_Tactic_FunInd_cleanPackedArgs___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_cleanPackedArgs___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__2___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__2___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__2___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__2___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___lambda__3___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__4 = _init_l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Tactic_FunInd_unpackMutualInduction___spec__1___closed__4);
l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__1 = _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__1);
l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__2 = _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__2);
l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__3 = _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__3();
lean_mark_persistent(l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__3);
l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__4 = _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__4();
lean_mark_persistent(l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__4);
l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__5 = _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__5();
lean_mark_persistent(l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__5);
l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__6 = _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__6();
lean_mark_persistent(l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__6);
l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__7 = _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__7();
lean_mark_persistent(l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__7);
l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__8 = _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__8();
lean_mark_persistent(l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__8);
l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__9 = _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__9();
lean_mark_persistent(l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__9);
l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__10 = _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__10();
lean_mark_persistent(l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__10);
l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__11 = _init_l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__11();
lean_mark_persistent(l_Lean_Tactic_FunInd_unpackMutualInduction___lambda__6___closed__11);
l_Lean_Tactic_FunInd_unpackMutualInduction___closed__1 = _init_l_Lean_Tactic_FunInd_unpackMutualInduction___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_unpackMutualInduction___closed__1);
l_Lean_Tactic_FunInd_unpackMutualInduction___closed__2 = _init_l_Lean_Tactic_FunInd_unpackMutualInduction___closed__2();
lean_mark_persistent(l_Lean_Tactic_FunInd_unpackMutualInduction___closed__2);
l_Lean_Tactic_FunInd_deriveInduction___closed__1 = _init_l_Lean_Tactic_FunInd_deriveInduction___closed__1();
lean_mark_persistent(l_Lean_Tactic_FunInd_deriveInduction___closed__1);
l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__1 = _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__1);
l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__2 = _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__2);
l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__3 = _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__3);
l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__4 = _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__4);
l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__5 = _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__5);
l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__6 = _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__6);
l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__7 = _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__7);
l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__8 = _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__8();
lean_mark_persistent(l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__8);
l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__9 = _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__9();
lean_mark_persistent(l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__9);
l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__10 = _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__10();
lean_mark_persistent(l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__10);
l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__11 = _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__11();
lean_mark_persistent(l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction___closed__11);
if (builtin) {res = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__1 = _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__1);
l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__2 = _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__2);
l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__3 = _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__3);
l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__4 = _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__4);
l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__5 = _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__5);
l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__6 = _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__6);
l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__7 = _init_l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Tactic_FunInd_elabDeriveInduction_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
