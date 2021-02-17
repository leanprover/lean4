// Lean compiler output
// Module: Lean.Elab.Tactic.Simp
// Imports: Init Lean.Meta.Tactic.Simp Lean.Elab.Tactic.Basic Lean.Elab.Tactic.ElabTerm Lean.Elab.Tactic.Location Lean.Meta.Tactic.Replace
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_simpAll___spec__1(lean_object*, lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSimpConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocalDecl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabSimpConfig___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__5;
lean_object* l_Lean_Elab_Tactic_withMainMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabSimpConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tryExactTrivial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocalDeclFVarId___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_resolveGlobalConstNoOverload___spec__2(lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocalDecl___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_getCongrLemmas___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpTarget___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tryExactTrivial_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabSimpConfig___closed__1;
lean_object* l_Lean_Elab_Tactic_simpTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_simpPost___closed__2;
extern lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1___rarg___closed__1;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BacktrackableState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabSimpConfig___closed__4;
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_match__2___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp(lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocalDecl___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalSimp___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocalDeclFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_match__3(lean_object*);
lean_object* l_List_map___at_Lean_resolveGlobalConst___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalSimp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpAll_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Meta_replaceLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_mkEmpty___closed__1;
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__2;
extern lean_object* l_Lean_instInhabitedException___closed__1;
lean_object* l_Lean_Elab_Tactic_simpTarget_match__2(lean_object*);
lean_object* l_Lean_Elab_Tactic_simpTarget_match__2___rarg(lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_resolveGlobalConstNoOverload___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSimpConfigUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_insert___closed__1;
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forM___at_Lean_Elab_Tactic_evalSimp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_Elab_Tactic_evalSimp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocalDecl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpAll___lambda__1___closed__3;
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_Elab_Tactic_simpAll___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabSimpConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Simp_DefaultMethods_methods;
lean_object* l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__3;
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__1;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocalDeclFVarId___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forM___at_Lean_Elab_Tactic_evalTacticAux___spec__10___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpTarget_match__1(lean_object*);
lean_object* l_List_filterAux___at_Lean_resolveGlobalConst___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tryExactTrivial___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSimp___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Simp_rewrite_getRHS___closed__3;
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_match__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_tryExactTrivial___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocalDeclFVarId_match__2(lean_object*);
lean_object* l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__3;
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__4;
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpLemmas___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalExact___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_try___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_1455____closed__1;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSimp_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_resolveGlobalConstNoOverload___rarg___lambda__1___closed__1;
lean_object* l_Lean_Meta_changeLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
extern lean_object* l_Lean_resolveGlobalConstNoOverload___rarg___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tryExactTrivial___closed__1;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSimp_match__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocalDeclFVarId_match__1(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Tactic_saveBacktrackableState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabSimpConfig___closed__3;
lean_object* l_Lean_Elab_Tactic_setGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tryExactTrivial_match__1(lean_object*);
lean_object* l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_simp___closed__2;
lean_object* l_Lean_Elab_Tactic_simpAll___lambda__1___closed__1;
lean_object* l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__2;
lean_object* l_Lean_Elab_Tactic_simpAll___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpTarget_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__1;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Term_evalExpr___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocalDeclFVarId_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpTarget___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocalDeclFVarId___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___boxed__const__1;
lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpAll___lambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_evalSimpConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Lean_Elab_Tactic_evalSimp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_withMacroExpansion___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forM___at_Lean_Elab_Tactic_evalSimp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Elab_Tactic_elabSimpConfig___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_match__2(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_simpAll___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_intro___closed__3;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_addConst(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocalDeclFVarId_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabSimpConfig___closed__2;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpAll_match__1(lean_object*);
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
lean_object* l_Lean_Elab_Tactic_evalSimpConfig___rarg(lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Elab_Tactic_elabSimpConfig___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withSynthesize___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocalDeclFVarId___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_simpTarget_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Tactic_simpTarget_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_simpTarget_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_simpTarget_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_simpTarget_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_simpTarget_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_simpTarget___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_4, 2);
lean_inc(x_14);
lean_dec(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_15 = l_Lean_Meta_instantiateMVars(x_14, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_Simp_DefaultMethods_methods;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_19 = l_Lean_Meta_Simp_main(x_16, x_1, x_18, x_9, x_10, x_11, x_12, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_24 = l_Lean_Meta_replaceTargetDefEq(x_2, x_23, x_9, x_10, x_11, x_12, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_3);
x_28 = l_Lean_Elab_Tactic_setGoals(x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_dec(x_19);
x_34 = lean_ctor_get(x_21, 0);
lean_inc(x_34);
lean_dec(x_21);
x_35 = lean_ctor_get(x_20, 0);
lean_inc(x_35);
lean_dec(x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_36 = l_Lean_Meta_replaceTargetEq(x_2, x_35, x_34, x_9, x_10, x_11, x_12, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_3);
x_40 = l_Lean_Elab_Tactic_setGoals(x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_38);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_36);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_19);
if (x_45 == 0)
{
return x_19;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_19, 0);
x_47 = lean_ctor_get(x_19, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_19);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_15);
if (x_49 == 0)
{
return x_15;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_15, 0);
x_51 = lean_ctor_get(x_15, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_15);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_simpTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExact___lambda__1___boxed), 10, 1);
lean_closure_set(x_16, 0, x_14);
lean_inc(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_simpTarget___lambda__1___boxed), 13, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_15);
x_18 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_withMacroExpansion___spec__2___rarg), 11, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_14, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l_Lean_Elab_Tactic_simpTarget___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_simpTarget___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
lean_object* l_Lean_Elab_Tactic_simpLocalDeclFVarId_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Tactic_simpLocalDeclFVarId_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_simpLocalDeclFVarId_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_simpLocalDeclFVarId_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_simpLocalDeclFVarId_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_simpLocalDeclFVarId_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_simpLocalDeclFVarId___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_getLocalDecl(x_1, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_simpLocalDeclFVarId___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_LocalDecl_type(x_5);
x_16 = l_Lean_Meta_Simp_DefaultMethods_methods;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_17 = l_Lean_Meta_Simp_main(x_15, x_1, x_16, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_23 = l_Lean_Meta_changeLocalDecl(x_2, x_3, x_21, x_22, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_4);
x_27 = l_Lean_Elab_Tactic_setGoals(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_25);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_ctor_get(x_19, 0);
lean_inc(x_33);
lean_dec(x_19);
x_34 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
lean_dec(x_18);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_35 = l_Lean_Meta_replaceLocalDecl(x_2, x_3, x_34, x_33, x_10, x_11, x_12, x_13, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_4);
x_40 = l_Lean_Elab_Tactic_setGoals(x_39, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_37);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
return x_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_35, 0);
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_35);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_17);
if (x_45 == 0)
{
return x_17;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_17, 0);
x_47 = lean_ctor_get(x_17, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_17);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_simpLocalDeclFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_2);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_simpLocalDeclFVarId___lambda__1___boxed), 10, 1);
lean_closure_set(x_17, 0, x_2);
lean_inc(x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_simpLocalDeclFVarId___lambda__2___boxed), 14, 4);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_15);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_16);
x_19 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_withMacroExpansion___spec__2___rarg), 11, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_15, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_20;
}
else
{
uint8_t x_21; 
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
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_simpLocalDeclFVarId___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_simpLocalDeclFVarId___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_simpLocalDeclFVarId___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_simpLocalDeclFVarId___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
lean_object* l_Lean_Elab_Tactic_simpLocalDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_getLocalDeclFromUserName(x_1, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_simpLocalDecl___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_LocalDecl_fvarId(x_2);
x_13 = l_Lean_Elab_Tactic_simpLocalDeclFVarId(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_simpLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_simpLocalDecl___lambda__1___boxed), 10, 1);
lean_closure_set(x_12, 0, x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_simpLocalDecl___lambda__2___boxed), 11, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_withMacroExpansion___spec__2___rarg), 11, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
lean_object* l_Lean_Elab_Tactic_simpLocalDecl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_simpLocalDecl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_simpLocalDecl___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_simpLocalDecl___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_simpAll_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_simpAll_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_simpAll_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_simpAll___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = x_4 < x_3;
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_box(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_simpLocalDeclFVarId), 11, 2);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_18);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Elab_Tactic_try___rarg(x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (x_5 == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = x_4 + x_23;
x_25 = lean_unbox(x_21);
lean_dec(x_21);
x_4 = x_24;
x_5 = x_25;
x_14 = x_22;
goto _start;
}
else
{
lean_object* x_27; size_t x_28; size_t x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_28 = 1;
x_29 = x_4 + x_28;
x_30 = 1;
x_4 = x_29;
x_5 = x_30;
x_14 = x_27;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_simpAll___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to simplify");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_simpAll___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_simpAll___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_simpAll___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_simpAll___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_simpAll___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = l_Lean_LocalContext_getFVarIds(x_3);
x_14 = l_Array_reverse___rarg(x_13);
x_15 = lean_array_get_size(x_14);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_simpAll___spec__1(x_1, x_14, x_16, x_17, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_1455____closed__1;
x_27 = l_Lean_Elab_Tactic_simpAll___lambda__1___closed__3;
x_28 = lean_box(0);
x_29 = l_Lean_Meta_throwTacticEx___rarg(x_26, x_25, x_27, x_28, x_8, x_9, x_10, x_11, x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_18);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_18, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_18, 0, x_36);
return x_18;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_dec(x_18);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_simpAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_simpTarget), 10, 1);
lean_closure_set(x_11, 0, x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_Elab_Tactic_try___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_simpAll___lambda__1___boxed), 12, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1___rarg___closed__1;
x_17 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_withMacroExpansion___spec__2___rarg), 11, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_15);
x_18 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_18;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_simpAll___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_simpAll___spec__1(x_1, x_2, x_15, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_18;
}
}
lean_object* l_Lean_Elab_Tactic_simpAll___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Elab_Tactic_simpAll___lambda__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_14;
}
}
lean_object* l_Lean_Elab_Tactic_tryExactTrivial_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_tryExactTrivial_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tryExactTrivial_match__1___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tryExactTrivial___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_rewrite_getRHS___closed__3;
x_2 = l_Lean_Parser_Tactic_intro___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tryExactTrivial___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_tryExactTrivial___closed__1;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_tryExactTrivial(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
lean_inc(x_13);
x_15 = l_Lean_Meta_getMVarType(x_13, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_Meta_Simp_rewrite_getRHS___closed__3;
x_20 = l_Lean_Expr_isConstOf(x_17, x_19);
lean_dec(x_17);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_13);
x_21 = lean_box(0);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_15);
x_22 = l_Lean_Elab_Tactic_tryExactTrivial___closed__2;
x_23 = l_Lean_Meta_assignExprMVar(x_13, x_22, x_5, x_6, x_7, x_8, x_18);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_Tactic_setGoals(x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = l_Lean_Meta_Simp_rewrite_getRHS___closed__3;
x_29 = l_Lean_Expr_isConstOf(x_26, x_28);
lean_dec(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_14);
lean_dec(x_13);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = l_Lean_Elab_Tactic_tryExactTrivial___closed__2;
x_33 = l_Lean_Meta_assignExprMVar(x_13, x_32, x_5, x_6, x_7, x_8, x_27);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Elab_Tactic_setGoals(x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_14);
lean_dec(x_13);
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_15);
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
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_tryExactTrivial___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_tryExactTrivial(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_550____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Simp");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__1;
x_2 = l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Config");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__3;
x_2 = l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimpConfigUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__5;
x_10 = l_Lean_Elab_Term_evalExpr___rarg(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimpConfig___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedException___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimpConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpConfig___rarg), 1, 0);
return x_8;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimpConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_evalSimpConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Elab_Tactic_elabSimpConfig___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_2(x_1, x_2, x_3);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(x_9, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Elab_Tactic_elabSimpConfig___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at_Lean_Elab_Tactic_elabSimpConfig___spec__1___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_elabSimpConfig___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_instantiateMVars(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Tactic_evalSimpConfigUnsafe(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__5;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfig___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabSimpConfig___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfig___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabSimpConfig___lambda__1), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabSimpConfig___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = 0;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 1, 10);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 3, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 4, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 5, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 6, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 7, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 8, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 9, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_elabSimpConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Syntax_isNone(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_box(0);
x_13 = l_Lean_Elab_Tactic_elabSimpConfig___closed__2;
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 11, 4);
lean_closure_set(x_16, 0, x_11);
lean_closure_set(x_16, 1, x_13);
lean_closure_set(x_16, 2, x_15);
lean_closure_set(x_16, 3, x_12);
x_17 = l_Lean_Elab_Tactic_elabSimpConfig___closed__3;
x_18 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg), 9, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withSynthesize___rarg___boxed), 9, 2);
lean_closure_set(x_21, 0, x_18);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at_Lean_Elab_Tactic_elabSimpConfig___spec__1___rarg), 8, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = l_Lean_LocalContext_mkEmpty___closed__1;
x_24 = l_Array_empty___closed__1;
x_25 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__1___rarg(x_23, x_24, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = l_Lean_Elab_Tactic_elabSimpConfig___closed__4;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_8);
return x_27;
}
}
}
lean_object* l_Lean_Elab_Tactic_elabSimpConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_elabSimpConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_8, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 5);
lean_inc(x_16);
lean_dec(x_8);
x_17 = l_Lean_ResolveName_resolveGlobalName(x_14, x_15, x_16, x_1);
lean_dec(x_15);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_8, 4);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 5);
lean_inc(x_22);
lean_dec(x_8);
x_23 = l_Lean_ResolveName_resolveGlobalName(x_20, x_21, x_22, x_1);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_box(0);
x_12 = l_Lean_mkConst(x_1, x_11);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_throwUnknownConstant___rarg___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_KernelException_toMessageData___closed__3;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__5(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_List_map___at_Lean_resolveGlobalConst___spec__2(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc(x_8);
lean_inc(x_1);
x_11 = l_Lean_resolveGlobalName___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_List_filterAux___at_Lean_resolveGlobalConst___spec__1(x_12, x_14);
x_16 = l_List_isEmpty___rarg(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__2___lambda__1(x_15, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_8);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_15);
x_19 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
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
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
lean_object* l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_8);
lean_inc(x_1);
x_11 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_Lean_mkConst(x_1, x_14);
x_16 = lean_expr_dbg_to_string(x_15);
lean_dec(x_15);
x_17 = l_Lean_resolveGlobalConstNoOverload___rarg___lambda__1___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_resolveGlobalConstNoOverload___rarg___lambda__1___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_List_map___at_Lean_resolveGlobalConstNoOverload___spec__1(x_14, x_12);
x_22 = l_List_toString___at_Lean_resolveGlobalConstNoOverload___spec__2(x_21);
x_23 = lean_string_append(x_20, x_22);
lean_dec(x_22);
x_24 = l_Lean_instInhabitedParserDescr___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__6(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_8);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_11, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_12, 0);
lean_inc(x_32);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_32);
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_dec(x_11);
x_34 = lean_ctor_get(x_12, 0);
lean_inc(x_34);
lean_dec(x_12);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_29);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_dec(x_11);
x_37 = lean_box(0);
x_38 = l_Lean_mkConst(x_1, x_37);
x_39 = lean_expr_dbg_to_string(x_38);
lean_dec(x_38);
x_40 = l_Lean_resolveGlobalConstNoOverload___rarg___lambda__1___closed__1;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Lean_resolveGlobalConstNoOverload___rarg___lambda__1___closed__2;
x_43 = lean_string_append(x_41, x_42);
x_44 = l_List_map___at_Lean_resolveGlobalConstNoOverload___spec__1(x_37, x_12);
x_45 = l_List_toString___at_Lean_resolveGlobalConstNoOverload___spec__2(x_44);
x_46 = lean_string_append(x_43, x_45);
lean_dec(x_45);
x_47 = l_Lean_instInhabitedParserDescr___closed__1;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__6(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_8);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_8);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_11);
if (x_52 == 0)
{
return x_11;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_11, 0);
x_54 = lean_ctor_get(x_11, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_11);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Syntax_isIdent(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Syntax_getId(x_1);
x_15 = l_Lean_Elab_Tactic_saveBacktrackableState___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_8);
x_18 = l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__1(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_16);
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
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
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_8);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
}
lean_object* l_Lean_resolveGlobalName___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_resolveGlobalName___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
lean_object* l_Lean_getConstInfo___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
x_16 = lean_environment_find(x_15, x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_11);
x_17 = lean_box(0);
x_18 = l_Lean_mkConst(x_1, x_17);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_throwUnknownConstant___rarg___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_KernelException_toMessageData___closed__3;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___spec__2(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_25);
return x_11;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_1);
x_29 = lean_environment_find(x_28, x_1);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_box(0);
x_31 = l_Lean_mkConst(x_1, x_30);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_throwUnknownConstant___rarg___closed__2;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_KernelException_toMessageData___closed__3;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___spec__2(x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_1);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_21; 
x_21 = x_3 < x_2;
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_13);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_88; 
x_23 = lean_array_uget(x_1, x_3);
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_26 = x_4;
} else {
 lean_dec_ref(x_4);
 x_26 = lean_box(0);
}
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_Syntax_getArg(x_23, x_27);
x_29 = l_Lean_Syntax_isNone(x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = l_Lean_Syntax_getArg(x_23, x_30);
lean_dec(x_23);
lean_inc(x_11);
x_88 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas_resolveSimpIdLemma_x3f(x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (x_29 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_Syntax_getArg(x_28, x_27);
lean_dec(x_28);
x_92 = l_Lean_Syntax_getKind(x_91);
x_93 = l_Lean_Parser_Tactic_simpPost___closed__2;
x_94 = lean_name_eq(x_92, x_93);
lean_dec(x_92);
x_32 = x_94;
x_33 = x_89;
x_34 = x_90;
goto block_87;
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_28);
x_95 = lean_ctor_get(x_88, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_88, 1);
lean_inc(x_96);
lean_dec(x_88);
x_97 = 1;
x_32 = x_97;
x_33 = x_95;
x_34 = x_96;
goto block_87;
}
block_87:
{
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_35 = lean_box(0);
x_36 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_37 = l_Lean_Elab_Tactic_elabTerm(x_31, x_35, x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_unsigned_to_nat(1000u);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_41 = l_Lean_Meta_SimpLemmas_add(x_25, x_38, x_32, x_40, x_35, x_9, x_10, x_11, x_12, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
if (lean_is_scalar(x_26)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_26;
}
lean_ctor_set(x_44, 0, x_24);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_14 = x_45;
x_15 = x_43;
goto block_20;
}
else
{
uint8_t x_46; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_41, 0);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
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
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_50 = !lean_is_exclusive(x_37);
if (x_50 == 0)
{
return x_37;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_37, 0);
x_52 = lean_ctor_get(x_37, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_37);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_31);
x_54 = lean_ctor_get(x_33, 0);
lean_inc(x_54);
lean_dec(x_33);
lean_inc(x_54);
x_55 = l_Lean_getConstInfo___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___spec__1(x_54, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_34);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_ConstantInfo_type(x_56);
lean_dec(x_56);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_59 = l_Lean_Meta_isProp(x_58, x_9, x_10, x_11, x_12, x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = l_Lean_NameSet_insert___closed__1;
x_64 = lean_box(0);
x_65 = l_Std_RBNode_insert___rarg(x_63, x_24, x_54, x_64);
if (lean_is_scalar(x_26)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_26;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_25);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_14 = x_67;
x_15 = x_62;
goto block_20;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_59, 1);
lean_inc(x_68);
lean_dec(x_59);
x_69 = lean_unsigned_to_nat(1000u);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_70 = l_Lean_Meta_SimpLemmas_addConst(x_25, x_54, x_32, x_69, x_9, x_10, x_11, x_12, x_68);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
if (lean_is_scalar(x_26)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_26;
}
lean_ctor_set(x_73, 0, x_24);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_14 = x_74;
x_15 = x_72;
goto block_20;
}
else
{
uint8_t x_75; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_75 = !lean_is_exclusive(x_70);
if (x_75 == 0)
{
return x_70;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_70, 0);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_70);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_54);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_79 = !lean_is_exclusive(x_59);
if (x_79 == 0)
{
return x_59;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_59, 0);
x_81 = lean_ctor_get(x_59, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_59);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_54);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_83 = !lean_is_exclusive(x_55);
if (x_83 == 0)
{
return x_55;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_55, 0);
x_85 = lean_ctor_get(x_55, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_55);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
}
block_20:
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = x_3 + x_17;
x_3 = x_18;
x_4 = x_16;
x_13 = x_15;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get(x_1, 4);
lean_inc(x_16);
lean_inc(x_12);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_14);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_12);
lean_ctor_set(x_17, 4, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Syntax_isNone(x_1);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = l_Lean_Syntax_getSepArgs(x_19);
lean_dec(x_19);
x_21 = l_Lean_NameSet_empty;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
x_23 = lean_array_get_size(x_20);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = lean_box_usize(x_24);
x_26 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___boxed__const__1;
x_27 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___spec__3___boxed), 13, 4);
lean_closure_set(x_27, 0, x_20);
lean_closure_set(x_27, 1, x_25);
lean_closure_set(x_27, 2, x_26);
lean_closure_set(x_27, 3, x_22);
x_28 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___lambda__1___boxed), 11, 1);
lean_closure_set(x_28, 0, x_2);
x_29 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_withMacroExpansion___spec__2___rarg), 11, 2);
lean_closure_set(x_29, 0, x_27);
lean_closure_set(x_29, 1, x_28);
x_30 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_16, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_30;
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_object* x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_11);
return x_35;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_getConstInfo___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_getConstInfo___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___spec__3(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
return x_12;
}
}
lean_object* l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_4, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalSimp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimp_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalSimp___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = x_3 == x_4;
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = lean_apply_11(x_1, x_5, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = x_3 + x_20;
x_3 = x_21;
x_5 = x_18;
x_14 = x_19;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_14);
return x_27;
}
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_Elab_Tactic_evalSimp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_4, x_5);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_3);
x_18 = lean_nat_dec_le(x_5, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_usize_of_nat(x_4);
x_21 = lean_usize_of_nat(x_5);
x_22 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalSimp___spec__3(x_1, x_3, x_20, x_21, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_22;
}
}
}
}
lean_object* l_Array_forM___at_Lean_Elab_Tactic_evalSimp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_closure((void*)(l_Array_forM___at_Lean_Elab_Tactic_evalTacticAux___spec__10___lambda__1___boxed), 12, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_box(0);
x_16 = l_Array_foldlMUnsafe___at_Lean_Elab_Tactic_evalSimp___spec__2(x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_tryExactTrivial(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimp___lambda__1___boxed), 10, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Elab_Tactic_elabSimpConfig(x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_getSimpLemmas___rarg(x_9, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_getCongrLemmas___rarg(x_9, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getArg(x_1, x_22);
x_24 = lean_box(0);
x_25 = l_Lean_NameSet_empty;
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_17);
lean_ctor_set(x_26, 2, x_20);
lean_ctor_set(x_26, 3, x_25);
lean_ctor_set(x_26, 4, x_24);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_27 = l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas(x_23, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_unsigned_to_nat(3u);
x_31 = l_Lean_Syntax_getArg(x_1, x_30);
x_32 = l_Lean_Elab_Tactic_expandOptLocation(x_31);
lean_dec(x_31);
x_33 = l_Lean_Elab_Tactic_evalSimp___closed__1;
switch (lean_obj_tag(x_32)) {
case 0:
{
lean_object* x_34; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Lean_Elab_Tactic_simpAll(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_10(x_33, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
case 1:
{
lean_object* x_42; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_42 = l_Lean_Elab_Tactic_simpTarget(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_apply_10(x_33, x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
default: 
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_32, 0);
lean_inc(x_50);
lean_dec(x_32);
x_51 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_simpLocalDecl), 11, 1);
lean_closure_set(x_51, 0, x_28);
x_52 = lean_array_get_size(x_50);
x_53 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_54 = l_Array_forM___at_Lean_Elab_Tactic_evalSimp___spec__1(x_51, x_50, x_53, x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_52);
lean_dec(x_50);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_apply_10(x_33, x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_56);
return x_57;
}
else
{
uint8_t x_58; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_54, 0);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_54);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_27);
if (x_62 == 0)
{
return x_27;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_27, 0);
x_64 = lean_ctor_get(x_27, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_27);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_13);
if (x_66 == 0)
{
return x_13;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_13, 0);
x_68 = lean_ctor_get(x_13, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_13);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalSimp___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalSimp___spec__3(x_1, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_17;
}
}
lean_object* l_Array_foldlMUnsafe___at_Lean_Elab_Tactic_evalSimp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_foldlMUnsafe___at_Lean_Elab_Tactic_evalSimp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
lean_object* l_Array_forM___at_Lean_Elab_Tactic_evalSimp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_forM___at_Lean_Elab_Tactic_evalSimp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimp___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_evalSimp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimp___boxed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_simp___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSimp___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Location(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Replace(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Tactic_Simp(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_simpAll___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_simpAll___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_simpAll___lambda__1___closed__1);
l_Lean_Elab_Tactic_simpAll___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_simpAll___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_simpAll___lambda__1___closed__2);
l_Lean_Elab_Tactic_simpAll___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_simpAll___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_simpAll___lambda__1___closed__3);
l_Lean_Elab_Tactic_tryExactTrivial___closed__1 = _init_l_Lean_Elab_Tactic_tryExactTrivial___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_tryExactTrivial___closed__1);
l_Lean_Elab_Tactic_tryExactTrivial___closed__2 = _init_l_Lean_Elab_Tactic_tryExactTrivial___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_tryExactTrivial___closed__2);
l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__1);
l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__2 = _init_l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__2);
l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__3 = _init_l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__3);
l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__4 = _init_l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__4);
l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__5 = _init_l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpConfigUnsafe___closed__5);
l_Lean_Elab_Tactic_elabSimpConfig___closed__1 = _init_l_Lean_Elab_Tactic_elabSimpConfig___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfig___closed__1);
l_Lean_Elab_Tactic_elabSimpConfig___closed__2 = _init_l_Lean_Elab_Tactic_elabSimpConfig___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfig___closed__2);
l_Lean_Elab_Tactic_elabSimpConfig___closed__3 = _init_l_Lean_Elab_Tactic_elabSimpConfig___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfig___closed__3);
l_Lean_Elab_Tactic_elabSimpConfig___closed__4 = _init_l_Lean_Elab_Tactic_elabSimpConfig___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_elabSimpConfig___closed__4);
l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___boxed__const__1 = _init_l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Simp_0__Lean_Elab_Tactic_elabSimpLemmas___boxed__const__1);
l_Lean_Elab_Tactic_evalSimp___closed__1 = _init_l_Lean_Elab_Tactic_evalSimp___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimp___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSimp___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimp___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimp___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalSimp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
