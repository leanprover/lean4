// Lean compiler output
// Module: Lean.Elab.Inductive
// Imports: Init Lean.Util.ReplaceLevel Lean.Util.ReplaceExpr Lean.Util.CollectLevelParams Lean.Meta.Constructions Lean.Meta.CollectFVars Lean.Meta.SizeOf Lean.Meta.Injective Lean.Meta.IndPredBelow Lean.Elab.Command Lean.Elab.DefView Lean.Elab.DeclUtil Lean.Elab.Deriving.Basic
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
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__1;
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_brec_on(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__7;
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__2;
size_t l_USize_add(size_t, size_t);
uint8_t l_Lean_Level_isNeverZero(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkTypeFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__4;
lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___closed__1;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___lambda__1(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkResultingUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___closed__2;
uint8_t l_Lean_Elab_Modifiers_isPartial(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkResultUniverse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instInhabitedElabHeaderResult;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instInhabitedInductiveView;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1(lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__1;
static lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__4;
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkResultingUniverses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedAttribute;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_cases_on(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_hasOutParams___spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Command_accLevelAtCtor___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkInjectiveTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_instHashableName;
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___closed__1;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureNoUnassignedMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___boxed__const__1;
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedCtorView___closed__3;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_accLevelAtCtor___closed__1;
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Elab_Term_applyAttributesAt(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_bootstrap_inductiveCheckResultingUniverse;
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_getOffsetAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2___closed__1;
lean_object* l_Lean_Elab_Term_getLevelNames___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_shouldInferResultUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_accLevelAtCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__1;
static lean_object* l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__10;
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLevelNames___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__2;
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__5;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2___closed__3;
lean_object* l_Lean_throwKernelException___at_Lean_Elab_Term_evalExpr___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkResultingUniverse___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkTypeFor___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkResultingUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__3;
lean_object* l_Std_HashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkResultingUniverse___closed__2;
lean_object* lean_mk_ibelow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSizeOfInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkResultUniverse___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBInductionOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInductiveViews___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBInductionOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls(lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__7;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_tmpIndParam___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_bootstrap_inductiveCheckResultingUniverse___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabInductiveViews___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInductiveViews(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Meta_reduce_visit___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_tmpIndParam___closed__1;
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_assignLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInductiveViews___lambda__2___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_ppExpr___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__2___boxed(lean_object**);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_Meta_Match_mkMatcher___spec__6(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__2;
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instHashableExpr;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5(uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instInhabitedCtorView;
static lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__3;
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeaders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_accLevelAtCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__2___closed__1;
lean_object* l_Lean_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__4;
lean_object* l_Lean_Elab_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__2___closed__1;
lean_object* l_Lean_Elab_Term_collectUsedFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeader___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedInductiveView___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__5;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__2;
static lean_object* l_Lean_Elab_Command_accLevelAtCtor___closed__2;
lean_object* l_Lean_addDecl___at_Lean_Elab_Term_evalExpr___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__6;
lean_object* l_Lean_Elab_DerivingClassView_applyHandlers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_accLevelAtCtor___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeaders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__3;
static lean_object* l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resetMessageLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__1;
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__3___closed__1;
lean_object* lean_mk_below(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_accLevelAtCtor___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
uint8_t l_Array_contains___at___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_instInhabitedBool;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInductiveViews___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__3;
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___closed__1;
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__3___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__4;
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkTypeFor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeader___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__3;
static lean_object* l_Lean_Elab_Command_tmpIndParam___closed__3;
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__4;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__4;
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__6;
lean_object* l_Lean_Level_mkNaryMax(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8___lambda__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInductiveViews___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__1;
static lean_object* l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__2;
extern lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache;
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__3;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInductiveViews___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__1;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__6;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__1;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_getLevelOffset(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabInductiveViews___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__1(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__3;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__2;
extern lean_object* l_Lean_Expr_instBEqExpr;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__8;
uint8_t l_Lean_Level_isZero(lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_inferImplicit(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___rarg___closed__2;
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_occurs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__6;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addAutoBoundImplicits(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__2___closed__1;
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__5;
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__4;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__3(uint8_t, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_rec_on(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Command_accLevelAtCtor___spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelOne;
uint8_t lean_level_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__1___closed__1;
uint8_t l_List_beq___at_Lean_OpenDecl_instToStringOpenDecl___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__2(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__5;
lean_object* l_Lean_Elab_Term_withAutoBoundImplicit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidInductiveModifier(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_tmpIndParam;
static lean_object* l_Lean_Elab_Command_instInhabitedCtorView___closed__1;
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_mk_binduction_on(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop(lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__2;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_instInhabitedCtorView___closed__2;
extern lean_object* l_Lean_Expr_ReplaceImpl_initCache;
static lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__4;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instBEqName;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inductive");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__2;
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__4;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of attributes in inductive declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("class");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_eq(x_6, x_9);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__2;
x_12 = l_Lean_throwError___rarg(x_2, x_3, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = l_Lean_Elab_instInhabitedAttribute;
x_14 = lean_array_get(x_13, x_5, x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__4;
x_17 = lean_name_eq(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__2;
x_19 = l_Lean_throwError___rarg(x_2, x_3, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = lean_apply_2(x_21, lean_box(0), x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_6);
lean_dec(x_3);
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
lean_dec(x_2);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = lean_apply_2(x_25, lean_box(0), x_26);
return x_27;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'partial' in inductive declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
x_6 = l_Lean_Elab_Modifiers_isPartial(x_1);
lean_dec(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__2___closed__2;
x_15 = l_Lean_throwError___rarg(x_2, x_3, x_14);
x_16 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_5);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'noncomputable' in inductive declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__2___boxed), 4, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_2);
x_5 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = l_Lean_Elab_Command_checkValidInductiveModifier___rarg___closed__2;
x_14 = l_Lean_throwError___rarg(x_1, x_2, x_13);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_14, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidInductiveModifier(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_checkValidInductiveModifier___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of attributes in constructor declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__1___closed__2;
x_10 = l_Lean_throwError___rarg(x_2, x_3, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'unsafe' in constructor declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
lean_dec(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__2___closed__2;
x_15 = l_Lean_throwError___rarg(x_2, x_3, x_14);
x_16 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_5);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'partial' in constructor declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__2___boxed), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
x_6 = l_Lean_Elab_Modifiers_isPartial(x_1);
lean_dec(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__3___closed__2;
x_15 = l_Lean_throwError___rarg(x_2, x_3, x_14);
x_16 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_5);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'noncomputable' in constructor declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__3___boxed), 4, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_2);
x_5 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = l_Lean_Elab_Command_checkValidCtorModifier___rarg___closed__2;
x_14 = l_Lean_throwError___rarg(x_1, x_2, x_13);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_14, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_checkValidCtorModifier___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedCtorView___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedCtorView___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = 0;
x_4 = 0;
x_5 = l_Lean_Elab_Command_instInhabitedCtorView___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedCtorView___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Elab_Command_instInhabitedCtorView___closed__2;
x_4 = 0;
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedCtorView() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instInhabitedCtorView___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedInductiveView___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lean_Elab_Command_instInhabitedCtorView___closed__2;
x_5 = lean_box(0);
x_6 = l_Lean_Elab_Command_instInhabitedCtorView___closed__1;
x_7 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_5);
lean_ctor_set(x_7, 4, x_2);
lean_ctor_set(x_7, 5, x_3);
lean_ctor_set(x_7, 6, x_1);
lean_ctor_set(x_7, 7, x_6);
lean_ctor_set(x_7, 8, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedInductiveView() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instInhabitedInductiveView___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_instInhabitedCtorView___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__5() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__4;
x_2 = l_Lean_Elab_Command_instInhabitedCtorView___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__5;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__3;
x_2 = l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static uint64_t _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__8() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__9() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__8;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_instInhabitedInductiveView___closed__1;
x_2 = l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__7;
x_3 = l_Lean_Elab_Command_instInhabitedCtorView___closed__1;
x_4 = l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__9;
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__10;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_13, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_8);
x_17 = l_Lean_Elab_Term_addAutoBoundImplicits(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
lean_dec(x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
x_21 = l_Lean_Meta_getLocalInstances(x_8, x_9, x_10, x_11, x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_18);
lean_ctor_set(x_24, 4, x_3);
x_25 = lean_array_push(x_4, x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_20);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set(x_28, 3, x_18);
lean_ctor_set(x_28, 4, x_3);
x_29 = lean_array_push(x_4, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_15);
if (x_35 == 0)
{
return x_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_15, 0);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_15);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid inductive type, resultant type is not a sort");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 6);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_12 = l_Lean_Meta_mkFreshLevelMVar(x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_mkSort(x_13);
x_16 = 0;
x_17 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_16, x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_6);
x_20 = l_Lean_Elab_Term_addAutoBoundImplicits(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
x_24 = l_Lean_Meta_getLocalInstances(x_6, x_7, x_8, x_9, x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_27, 3, x_21);
lean_ctor_set(x_27, 4, x_15);
x_28 = lean_array_push(x_2, x_27);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_21);
lean_ctor_set(x_31, 4, x_15);
x_32 = lean_array_push(x_2, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
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
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_18);
if (x_38 == 0)
{
return x_18;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_18, 0);
x_40 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_18);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_11, 0);
lean_inc(x_42);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_42);
x_43 = l_Lean_Elab_Term_elabType(x_42, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_44);
x_46 = l_Lean_Meta_isTypeFormerType(x_44, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_44);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__2;
x_51 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(x_42, x_50, x_4, x_5, x_6, x_7, x_8, x_9, x_49);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_42);
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
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_42);
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
lean_dec(x_46);
x_57 = lean_box(0);
x_58 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__1(x_3, x_1, x_44, x_2, x_57, x_4, x_5, x_6, x_7, x_8, x_9, x_56);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_46);
if (x_59 == 0)
{
return x_46;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_46, 0);
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_46);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_43);
if (x_63 == 0)
{
return x_43;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_43, 0);
x_65 = lean_ctor_get(x_43, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_43);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_array_fget(x_1, x_2);
x_15 = lean_ctor_get(x_14, 5);
lean_inc(x_15);
x_16 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2), 10, 2);
lean_closure_set(x_17, 0, x_14);
lean_closure_set(x_17, 1, x_3);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Elab_Term_withAutoBoundImplicit___rarg(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
lean_dec(x_2);
x_2 = x_23;
x_3 = x_20;
x_10 = x_21;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid inductive type, number of parameters mismatch in mutually inductive datatypes");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_4 < x_3;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
lean_dec(x_16);
x_18 = lean_nat_dec_eq(x_17, x_1);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__2;
x_22 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(x_20, x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
lean_dec(x_15);
x_27 = 1;
x_28 = x_4 + x_27;
x_29 = lean_box(0);
x_4 = x_28;
x_5 = x_29;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lean_Elab_Command_instInhabitedElabHeaderResult;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get(x_9, x_1, x_10);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_array_get_size(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_1);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = lean_box(0);
x_18 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1(x_13, x_1, x_15, x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_13);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid inductive type, cannot mix unsafe and safe declarations in a mutually inductive datatypes");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_4 < x_3;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*2 + 3);
lean_dec(x_17);
if (x_18 == 0)
{
if (x_1 == 0)
{
uint8_t x_32; 
x_32 = 1;
x_19 = x_32;
goto block_31;
}
else
{
uint8_t x_33; 
x_33 = 0;
x_19 = x_33;
goto block_31;
}
}
else
{
if (x_1 == 0)
{
uint8_t x_34; 
x_34 = 0;
x_19 = x_34;
goto block_31;
}
else
{
uint8_t x_35; 
x_35 = 1;
x_19 = x_35;
goto block_31;
}
}
block_31:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___closed__2;
x_22 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(x_20, x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
lean_dec(x_16);
x_27 = 1;
x_28 = x_4 + x_27;
x_29 = lean_box(0);
x_4 = x_28;
x_5 = x_29;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_9 = l_Lean_Elab_Command_instInhabitedElabHeaderResult;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get(x_9, x_1, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*2 + 3);
lean_dec(x_13);
x_15 = lean_array_get_size(x_1);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = lean_box(0);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1(x_14, x_1, x_16, x_17, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1(x_13, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid inductive type, universe parameters mismatch in mutually inductive datatypes");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_4 < x_3;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_15, 4);
lean_inc(x_16);
x_17 = l_List_beq___at_Lean_OpenDecl_instToStringOpenDecl___spec__1(x_16, x_1);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__2;
x_20 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_18);
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
size_t x_25; size_t x_26; lean_object* x_27; 
lean_dec(x_15);
x_25 = 1;
x_26 = x_4 + x_25;
x_27 = lean_box(0);
x_4 = x_26;
x_5 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_lt(x_10, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_14 = l_Lean_Elab_Command_instInhabitedInductiveView;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get(x_14, x_1, x_15);
x_17 = lean_ctor_get(x_16, 4);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_19 = 0;
x_20 = lean_box(0);
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1(x_17, x_1, x_18, x_19, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_17);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkTypeFor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = 1;
x_12 = l_Lean_Meta_mkForallFVars(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkTypeFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkTypeFor___lambda__1___boxed), 9, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__3___rarg(x_9, x_10, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkTypeFor___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkTypeFor___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected inductive resulting type");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__2;
x_9 = l_Lean_throwError___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___spec__1___rarg(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_isExprDefEq(x_3, x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___lambda__1___boxed), 8, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1___rarg___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_10(x_1, x_4, x_5, x_6, x_2, x_3, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeCompatible___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeCompatible___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__2___lambda__1), 11, 3);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_6);
x_13 = l_Lean_Elab_Command_instInhabitedCtorView___closed__1;
x_14 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg(x_12, x_3, x_1, x_2, x_13, x_7, x_8, x_9, x_10, x_11);
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
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resulting universe mismatch, given");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nexpected type");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_3);
x_11 = l_Lean_Meta_isExprDefEq(x_3, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_indentExpr(x_1);
x_16 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_indentExpr(x_3);
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__6;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_11, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_11, 0, x_27);
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_dec(x_11);
x_29 = lean_box(0);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
return x_11;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_11, 0);
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_11);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_3);
lean_dec(x_1);
x_35 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__2;
x_36 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_35, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___boxed), 10, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1___rarg(x_1, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__2), 10, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1___rarg(x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__3), 10, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid mutually inductive types, ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__1;
x_12 = l_Lean_Meta_forallTelescopeCompatible___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__2(x_1, x_2, x_3, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__3;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__6;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_13, 1, x_21);
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__3;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__6;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_12, 0, x_28);
return x_12;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_dec(x_12);
x_30 = lean_ctor_get(x_13, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_32 = x_13;
} else {
 lean_dec_ref(x_13);
 x_32 = lean_box(0);
}
x_33 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__3;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
x_35 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__6;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
if (lean_is_scalar(x_32)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_32;
}
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_29);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_12);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_12, 0);
lean_dec(x_40);
return x_12;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_12, 1);
lean_inc(x_41);
lean_dec(x_12);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_13);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_11 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkTypeFor(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 3);
x_23 = l_Lean_replaceRef(x_20, x_22);
lean_dec(x_22);
lean_dec(x_20);
lean_ctor_set(x_8, 3, x_23);
lean_inc(x_18);
x_24 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType(x_16, x_18, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_18);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_18);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_8, 0);
x_34 = lean_ctor_get(x_8, 1);
x_35 = lean_ctor_get(x_8, 2);
x_36 = lean_ctor_get(x_8, 3);
x_37 = lean_ctor_get(x_8, 4);
x_38 = lean_ctor_get(x_8, 5);
x_39 = lean_ctor_get(x_8, 6);
x_40 = lean_ctor_get(x_8, 7);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_8);
x_41 = l_Lean_replaceRef(x_20, x_36);
lean_dec(x_36);
lean_dec(x_20);
x_42 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 2, x_35);
lean_ctor_set(x_42, 3, x_41);
lean_ctor_set(x_42, 4, x_37);
lean_ctor_set(x_42, 5, x_38);
lean_ctor_set(x_42, 6, x_39);
lean_ctor_set(x_42, 7, x_40);
lean_inc(x_18);
x_43 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType(x_16, x_18, x_2, x_4, x_5, x_6, x_7, x_42, x_9, x_17);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_18);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_18);
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_49 = x_43;
} else {
 lean_dec_ref(x_43);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_11);
if (x_51 == 0)
{
return x_11;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_11, 0);
x_53 = lean_ctor_get(x_11, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_11);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeaders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Elab_Command_instInhabitedElabHeaderResult;
x_17 = lean_array_get(x_16, x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_18 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeader(x_17, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
lean_dec(x_3);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_19);
x_3 = x_22;
x_4 = x_23;
x_11 = x_20;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeaders___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeaders(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeader___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Elab_Command_instInhabitedCtorView___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux(x_1, x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_array_get_size(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_dec_lt(x_16, x_15);
lean_dec(x_15);
if (x_17 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_18; 
lean_free_object(x_11);
lean_inc(x_6);
lean_inc(x_2);
x_18 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeaders(x_13, x_21, x_9, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_13);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
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
uint8_t x_33; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
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
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
x_43 = lean_array_get_size(x_41);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_dec_lt(x_44, x_43);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
else
{
lean_object* x_47; 
lean_inc(x_6);
lean_inc(x_2);
x_47 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
lean_inc(x_6);
lean_inc(x_2);
x_49 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_box(0);
x_53 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeaders(x_41, x_50, x_9, x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_51);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_41);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_41);
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_59 = x_53;
} else {
 lean_dec_ref(x_53);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_ctor_get(x_49, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_49, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_63 = x_49;
} else {
 lean_dec_ref(x_49);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = lean_ctor_get(x_47, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_47, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_67 = x_47;
} else {
 lean_dec_ref(x_47);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_11);
if (x_69 == 0)
{
return x_11;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_11, 0);
x_71 = lean_ctor_get(x_11, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_11);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeader___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeader___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeader(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
lean_dec(x_1);
x_16 = lean_array_push(x_2, x_6);
x_17 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg(x_3, x_4, x_5, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_2);
x_14 = lean_nat_dec_lt(x_4, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_apply_9(x_1, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_2, x_4);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg___lambda__1), 13, 5);
lean_closure_set(x_19, 0, x_4);
lean_closure_set(x_19, 1, x_5);
lean_closure_set(x_19, 2, x_1);
lean_closure_set(x_19, 3, x_2);
lean_closure_set(x_19, 4, x_3);
x_20 = 0;
x_21 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg(x_17, x_20, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_2 < x_1;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = x_3;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = x_14;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_17);
x_18 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkTypeFor(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
x_24 = 1;
x_25 = x_2 + x_24;
x_26 = x_23;
x_27 = lean_array_uset(x_16, x_2, x_26);
x_2 = x_25;
x_3 = x_27;
x_10 = x_20;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 3);
x_15 = l_Lean_replaceRef(x_1, x_14);
lean_dec(x_14);
lean_ctor_set(x_10, 3, x_15);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg(x_2, x_3, x_4, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
x_20 = lean_ctor_get(x_10, 2);
x_21 = lean_ctor_get(x_10, 3);
x_22 = lean_ctor_get(x_10, 4);
x_23 = lean_ctor_get(x_10, 5);
x_24 = lean_ctor_get(x_10, 6);
x_25 = lean_ctor_get(x_10, 7);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_26 = l_Lean_replaceRef(x_1, x_21);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_27, 4, x_22);
lean_ctor_set(x_27, 5, x_23);
lean_ctor_set(x_27, 6, x_24);
lean_ctor_set(x_27, 7, x_25);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg(x_2, x_3, x_4, x_28, x_5, x_6, x_7, x_8, x_9, x_27, x_11, x_12);
return x_29;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
lean_inc(x_1);
x_12 = x_1;
x_13 = lean_box_usize(x_11);
x_14 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___boxed__const__1;
x_15 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___spec__1___boxed), 10, 3);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_12);
x_16 = x_15;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = lean_apply_7(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Command_instInhabitedElabHeaderResult;
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get(x_20, x_1, x_21);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Elab_Command_instInhabitedCtorView___closed__1;
x_29 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___lambda__1___boxed), 12, 5);
lean_closure_set(x_29, 0, x_27);
lean_closure_set(x_29, 1, x_2);
lean_closure_set(x_29, 2, x_18);
lean_closure_set(x_29, 3, x_23);
lean_closure_set(x_29, 4, x_28);
x_30 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__3___rarg(x_24, x_25, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_1, x_11);
lean_dec(x_11);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_infer_type(x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily___lambda__1___boxed), 10, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1___rarg(x_11, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_set(x_3, x_1, x_2);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inductive datatype parameter mismatch");
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nexpected");
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_nat_dec_le(x_11, x_4);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_3, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_3, x_15);
lean_dec(x_3);
x_17 = l_Lean_instInhabitedExpr;
x_18 = lean_array_get(x_17, x_1, x_4);
x_19 = lean_array_get(x_17, x_5, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_19);
lean_inc(x_18);
x_20 = l_Lean_Meta_isExprDefEq(x_18, x_19, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_indentExpr(x_19);
x_25 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__2;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__4;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_indentExpr(x_18);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__6;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_32, x_6, x_7, x_8, x_9, x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_19);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_dec(x_20);
x_39 = lean_box(0);
x_40 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___lambda__1(x_4, x_18, x_5, x_39, x_6, x_7, x_8, x_9, x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_2, 2);
x_45 = lean_nat_add(x_4, x_44);
lean_dec(x_4);
x_3 = x_16;
x_4 = x_45;
x_5 = x_43;
x_10 = x_42;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_20);
if (x_47 == 0)
{
return x_20;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_20, 0);
x_49 = lean_ctor_get(x_20, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_20);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_5);
lean_ctor_set(x_51, 1, x_10);
return x_51;
}
}
else
{
lean_object* x_52; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_5);
lean_ctor_set(x_52, 1, x_10);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_unsigned_to_nat(1u);
lean_inc(x_10);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_12);
x_14 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1(x_1, x_13, x_10, x_11, x_3, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_mkAppN(x_2, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = l_Lean_mkAppN(x_2, x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected inductive type occurrence");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Expr_getAppFn(x_3);
x_10 = l_Array_contains___at___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f___spec__1(x_1, x_9);
lean_dec(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Expr_getAppNumArgsAux(x_3, x_13);
x_15 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2___closed__1;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
lean_inc(x_3);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_3, x_16, x_18);
x_20 = lean_array_get_size(x_2);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_le(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_2);
x_23 = l_Lean_indentExpr(x_3);
x_24 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2___closed__3;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__6;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_27, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_3);
x_33 = lean_box(0);
x_34 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__1(x_2, x_9, x_19, x_33, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__3___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2), 8, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___closed__1;
x_11 = l_Lean_Meta_transform___at_Lean_Meta_expandCoe___spec__1(x_3, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_mkAppN(x_1, x_2);
x_13 = lean_apply_8(x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected constructor resulting type, type expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_Meta_isType(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_indentExpr(x_1);
x_15 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__2___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__6;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
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
lean_dec(x_3);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_10, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_box(0);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected constructor resulting type");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_2);
x_11 = l_Lean_Expr_getAppFn(x_3);
x_12 = lean_expr_eqv(x_11, x_1);
lean_dec(x_1);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = l_Lean_indentExpr(x_3);
x_14 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__3___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__6;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__2(x_3, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_24;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constructor resulting type must be specified in inductive family declaration");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_5, 4);
lean_inc(x_14);
lean_dec(x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_dec(x_1);
if (x_4 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__1(x_2, x_3, x_6, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_17 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___closed__2;
x_18 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_24 = l_Lean_Elab_Term_elabType(x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = 1;
x_28 = 0;
x_29 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_30 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_27, x_28, x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_32 = l_Lean_Meta_instantiateMVars(x_25, x_9, x_10, x_11, x_12, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_35 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs(x_1, x_3, x_33, x_9, x_10, x_11, x_12, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__3), 10, 1);
lean_closure_set(x_38, 0, x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_36);
x_39 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1___rarg(x_36, x_38, x_7, x_8, x_9, x_10, x_11, x_12, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_apply_8(x_6, x_36, x_7, x_8, x_9, x_10, x_11, x_12, x_40);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_36);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_35);
if (x_46 == 0)
{
return x_35;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_35, 0);
x_48 = lean_ctor_get(x_35, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_35);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_32);
if (x_50 == 0)
{
return x_32;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_32, 0);
x_52 = lean_ctor_get(x_32, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_32);
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
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_30);
if (x_54 == 0)
{
return x_30;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_30, 0);
x_56 = lean_ctor_get(x_30, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_30);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_24);
if (x_58 == 0)
{
return x_24;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_24, 0);
x_60 = lean_ctor_get(x_24, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_24);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_12, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_7);
x_16 = l_Lean_Elab_Term_addAutoBoundImplicits(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
lean_dec(x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
lean_inc(x_7);
x_20 = l_Lean_Meta_mkForallFVars(x_17, x_4, x_12, x_19, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_mkForallFVars(x_2, x_21, x_12, x_19, x_7, x_8, x_9, x_10, x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = lean_ctor_get(x_3, 2);
lean_inc(x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
return x_20;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_20, 0);
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_20);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_16);
if (x_41 == 0)
{
return x_16;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_16, 0);
x_43 = lean_ctor_get(x_16, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_16);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_inc(x_1);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___lambda__1___boxed), 11, 3);
lean_closure_set(x_15, 0, x_6);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_1);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 3);
x_18 = l_Lean_replaceRef(x_14, x_17);
lean_dec(x_17);
lean_dec(x_14);
lean_ctor_set(x_11, 3, x_18);
x_19 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType(x_3, x_4, x_2, x_5, x_1, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
x_22 = lean_ctor_get(x_11, 2);
x_23 = lean_ctor_get(x_11, 3);
x_24 = lean_ctor_get(x_11, 4);
x_25 = lean_ctor_get(x_11, 5);
x_26 = lean_ctor_get(x_11, 6);
x_27 = lean_ctor_get(x_11, 7);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_28 = l_Lean_replaceRef(x_14, x_23);
lean_dec(x_23);
lean_dec(x_14);
x_29 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set(x_29, 4, x_24);
lean_ctor_set(x_29, 5, x_25);
lean_ctor_set(x_29, 6, x_26);
lean_ctor_set(x_29, 7, x_27);
x_30 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType(x_3, x_4, x_2, x_5, x_1, x_15, x_7, x_8, x_9, x_10, x_29, x_12, x_13);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_ctor_get(x_16, 3);
lean_inc(x_18);
x_19 = l_Lean_Syntax_getArgs(x_18);
lean_dec(x_18);
x_20 = lean_box(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_21 = lean_alloc_closure((void*)(l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___lambda__2___boxed), 13, 5);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_3);
lean_closure_set(x_21, 2, x_1);
lean_closure_set(x_21, 3, x_2);
lean_closure_set(x_21, 4, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_21);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_23 = l_Lean_Elab_Term_withAutoBoundImplicit___rarg(x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1(x_1, x_2, x_3, x_4, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_ctor_set(x_5, 1, x_28);
lean_ctor_set(x_5, 0, x_24);
lean_ctor_set(x_26, 0, x_5);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_26);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_24);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_24);
lean_free_object(x_5);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
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
lean_free_object(x_5);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_5, 0);
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_5);
x_42 = lean_ctor_get(x_40, 3);
lean_inc(x_42);
x_43 = l_Lean_Syntax_getArgs(x_42);
lean_dec(x_42);
x_44 = lean_box(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_45 = lean_alloc_closure((void*)(l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___lambda__2___boxed), 13, 5);
lean_closure_set(x_45, 0, x_40);
lean_closure_set(x_45, 1, x_3);
lean_closure_set(x_45, 2, x_1);
lean_closure_set(x_45, 3, x_2);
lean_closure_set(x_45, 4, x_44);
x_46 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_46, 0, x_43);
lean_closure_set(x_46, 1, x_45);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = l_Lean_Elab_Term_withAutoBoundImplicit___rarg(x_46, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1(x_1, x_2, x_3, x_4, x_41, x_6, x_7, x_8, x_9, x_10, x_11, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_51);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_48);
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_58 = x_50;
} else {
 lean_dec_ref(x_50);
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
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_41);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_ctor_get(x_47, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_47, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_62 = x_47;
} else {
 lean_dec_ref(x_47);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_array_get_size(x_3);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 3);
x_17 = l_Lean_replaceRef(x_13, x_16);
lean_dec(x_16);
lean_dec(x_13);
lean_ctor_set(x_9, 3, x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_18 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily(x_14, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_12, 7);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_array_to_list(lean_box(0), x_21);
x_23 = lean_unbox(x_19);
lean_dec(x_19);
x_24 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1(x_1, x_2, x_3, x_23, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
x_31 = lean_ctor_get(x_9, 2);
x_32 = lean_ctor_get(x_9, 3);
x_33 = lean_ctor_get(x_9, 4);
x_34 = lean_ctor_get(x_9, 5);
x_35 = lean_ctor_get(x_9, 6);
x_36 = lean_ctor_get(x_9, 7);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_37 = l_Lean_replaceRef(x_13, x_32);
lean_dec(x_32);
lean_dec(x_13);
x_38 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_30);
lean_ctor_set(x_38, 2, x_31);
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set(x_38, 4, x_33);
lean_ctor_set(x_38, 5, x_34);
lean_ctor_set(x_38, 6, x_35);
lean_ctor_set(x_38, 7, x_36);
lean_inc(x_10);
lean_inc(x_38);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_39 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily(x_14, x_2, x_5, x_6, x_7, x_8, x_38, x_10, x_11);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_12, 7);
lean_inc(x_42);
lean_dec(x_12);
x_43 = lean_array_to_list(lean_box(0), x_42);
x_44 = lean_unbox(x_40);
lean_dec(x_40);
x_45 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1(x_1, x_2, x_3, x_44, x_43, x_5, x_6, x_7, x_8, x_38, x_10, x_41);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_38);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_48 = x_39;
} else {
 lean_dec_ref(x_39);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Elab_Term_levelMVarToParam_x27(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_ctor_set(x_13, 1, x_18);
x_20 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_1, 1, x_22);
lean_ctor_set(x_20, 0, x_1);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_1, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = l_Lean_Elab_Term_levelMVarToParam_x27(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_32);
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_1);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_42 = x_38;
} else {
 lean_dec_ref(x_38);
 x_42 = lean_box(0);
}
x_43 = l_Lean_Elab_Term_levelMVarToParam_x27(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
if (lean_is_scalar(x_42)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_42;
}
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_48);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = l_Lean_Elab_Term_levelMVarToParam_x27(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set(x_13, 2, x_22);
lean_ctor_set(x_13, 1, x_19);
x_24 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_24, 0, x_1);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_24);
lean_ctor_set(x_1, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_30 = lean_ctor_get(x_1, 1);
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
x_33 = lean_ctor_get(x_13, 2);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
x_34 = l_Lean_Elab_Term_levelMVarToParam_x27(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_38);
x_41 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2(x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
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
lean_ctor_set(x_1, 1, x_42);
lean_ctor_set(x_1, 0, x_40);
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_46 = lean_ctor_get(x_1, 0);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_1);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 2);
lean_inc(x_50);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 x_51 = x_46;
} else {
 lean_dec_ref(x_46);
 x_51 = lean_box(0);
}
x_52 = l_Lean_Elab_Term_levelMVarToParam_x27(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
if (lean_is_scalar(x_51)) {
 x_58 = lean_alloc_ctor(0, 3, 0);
} else {
 x_58 = x_51;
}
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_53);
lean_ctor_set(x_58, 2, x_56);
x_59 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2(x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_60);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_7, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_13, x_19);
lean_dec(x_13);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_16);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected inductive type resulting type");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_dec(x_1);
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___lambda__1___closed__2;
x_13 = l_Lean_throwError___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___spec__1(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected empty inductive declaration");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___lambda__1), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__2;
x_10 = l_Lean_throwError___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___spec__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__3;
x_14 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1___rarg(x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Command_tmpIndParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_tmp_ind_univ_param");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_tmpIndParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_tmpIndParam___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_tmpIndParam___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_tmpIndParam___closed__2;
x_2 = l_Lean_mkLevelParam(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_tmpIndParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_tmpIndParam___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cannot infer resulting universe level of inductive datatype, given level contains metavariables ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", provide universe explicitly");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_shouldInferResultUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_Level_hasMVar(x_11);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_2);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; 
lean_free_object(x_9);
x_16 = l_Lean_Level_getLevelOffset(x_11);
if (lean_obj_tag(x_16) == 5)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Elab_Command_tmpIndParam;
x_19 = l_Lean_Elab_Term_assignLevelMVar(x_17, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = 1;
x_23 = lean_box(x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_16);
x_28 = l_Lean_mkSort(x_11);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__2;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__4;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__1(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_9, 0);
x_36 = lean_ctor_get(x_9, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_9);
x_37 = l_Lean_Level_hasMVar(x_35);
if (x_37 == 0)
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_35);
lean_dec(x_2);
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Level_getLevelOffset(x_35);
if (lean_obj_tag(x_41) == 5)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_35);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Elab_Command_tmpIndParam;
x_44 = l_Lean_Elab_Term_assignLevelMVar(x_42, x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_36);
lean_dec(x_2);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = 1;
x_48 = lean_box(x_47);
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
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_41);
x_50 = l_Lean_mkSort(x_35);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__2;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__4;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__1(x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_36);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_shouldInferResultUniverse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Command_accLevelAtCtor___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_level_eq(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_3 + x_8;
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
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at_Lean_Elab_Command_accLevelAtCtor___spec__2(x_2, x_1, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_accLevelAtCtor___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_accLevelAtCtor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to compute resulting universe level of inductive datatype, provide universe explicitly");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_accLevelAtCtor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_accLevelAtCtor___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_accLevelAtCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_11);
return x_25;
}
case 1:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_3, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_3, x_29);
lean_dec(x_3);
x_1 = x_26;
x_3 = x_30;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_26);
lean_dec(x_3);
x_32 = lean_level_eq(x_1, x_2);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Level_occurs(x_2, x_1);
lean_dec(x_2);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_8);
lean_dec(x_5);
x_34 = l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___spec__1(x_4, x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_array_push(x_4, x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_11);
return x_36;
}
else
{
lean_object* x_37; 
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_11);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_4);
lean_dec(x_1);
x_38 = l_Lean_Elab_Command_accLevelAtCtor___closed__2;
x_39 = l_Lean_throwError___at_Lean_Elab_Command_accLevelAtCtor___spec__3(x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_11);
return x_40;
}
}
}
case 4:
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_nat_dec_eq(x_3, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_box(0);
x_12 = x_43;
goto block_24;
}
else
{
uint8_t x_44; 
x_44 = lean_level_eq(x_1, x_2);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_box(0);
x_12 = x_45;
goto block_24;
}
else
{
lean_object* x_46; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_11);
return x_46;
}
}
}
case 5:
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_nat_dec_eq(x_3, x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_box(0);
x_12 = x_49;
goto block_24;
}
else
{
uint8_t x_50; 
x_50 = lean_level_eq(x_1, x_2);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_box(0);
x_12 = x_51;
goto block_24;
}
else
{
lean_object* x_52; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_4);
lean_ctor_set(x_52, 1, x_11);
return x_52;
}
}
}
default: 
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_55 = l_Lean_Elab_Command_accLevelAtCtor(x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_1 = x_54;
x_4 = x_56;
x_11 = x_57;
goto _start;
}
else
{
uint8_t x_59; 
lean_dec(x_54);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_55);
if (x_59 == 0)
{
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_55);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
block_24:
{
uint8_t x_13; 
lean_dec(x_12);
x_13 = l_Lean_Level_occurs(x_2, x_1);
lean_dec(x_2);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_3);
lean_dec(x_3);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_5);
x_16 = l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___spec__1(x_4, x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_push(x_4, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
lean_dec(x_1);
x_20 = l_Lean_Elab_Command_accLevelAtCtor___closed__2;
x_21 = l_Lean_throwError___at_Lean_Elab_Command_accLevelAtCtor___spec__3(x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = l_Lean_Elab_Command_accLevelAtCtor___closed__2;
x_23 = l_Lean_throwError___at_Lean_Elab_Command_accLevelAtCtor___spec__3(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Command_accLevelAtCtor___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_Command_accLevelAtCtor___spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_accLevelAtCtor___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Command_accLevelAtCtor___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_accLevelAtCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_accLevelAtCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_expr_instantiate1(x_1, x_6);
lean_dec(x_6);
lean_dec(x_1);
x_15 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux(x_2, x_3, x_4, x_14, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_expr_instantiate1(x_1, x_5);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux(x_2, x_3, x_14, x_13, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_3, x_13);
if (x_14 == 0)
{
if (lean_obj_tag(x_4) == 7)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_3, x_19);
x_21 = (uint8_t)((x_18 << 24) >> 61);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___lambda__1), 13, 5);
lean_closure_set(x_22, 0, x_17);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_20);
lean_closure_set(x_22, 4, x_5);
x_23 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg(x_15, x_21, x_16, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_12);
return x_24;
}
}
else
{
if (lean_obj_tag(x_4) == 7)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_4, 2);
lean_inc(x_27);
x_28 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_26);
x_29 = l_Lean_Meta_getLevel(x_26, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_30, x_8, x_9, x_10, x_11, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_35 = l_Lean_Elab_Command_accLevelAtCtor(x_33, x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = (uint8_t)((x_28 << 24) >> 61);
x_39 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___lambda__2), 12, 4);
lean_closure_set(x_39, 0, x_27);
lean_closure_set(x_39, 1, x_1);
lean_closure_set(x_39, 2, x_2);
lean_closure_set(x_39, 3, x_36);
x_40 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda_loop___spec__1___rarg(x_25, x_38, x_26, x_39, x_6, x_7, x_8, x_9, x_10, x_11, x_37);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
uint8_t x_45; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_29);
if (x_45 == 0)
{
return x_29;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_29, 0);
x_47 = lean_ctor_get(x_29, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_29);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_5);
lean_ctor_set(x_49, 1, x_12);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux(x_1, x_2, x_4, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_4 = x_15;
x_5 = x_18;
x_12 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_List_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__1(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_4 = x_15;
x_5 = x_18;
x_12 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Elab_Command_instInhabitedCtorView___closed__1;
x_13 = l_List_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__2(x_1, x_2, x_3, x_4, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkResultUniverse(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Array_isEmpty___rarg(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_array_to_list(lean_box(0), x_1);
x_5 = l_Lean_Level_mkNaryMax(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Level_normalize(x_5);
lean_dec(x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = l_Lean_Level_isZero(x_5);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Level_isNeverZero(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_levelOne;
x_12 = l_Lean_mkLevelMax(x_5, x_11);
x_13 = l_Lean_Level_normalize(x_12);
lean_dec(x_12);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Level_normalize(x_5);
lean_dec(x_5);
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Level_normalize(x_5);
lean_dec(x_5);
return x_15;
}
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_2, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_array_to_list(lean_box(0), x_1);
x_19 = l_Lean_Level_mkNaryMax(x_18);
x_20 = l_Lean_Level_normalize(x_19);
lean_dec(x_19);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = l_Lean_levelOne;
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_mkResultUniverse___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_mkResultUniverse(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_1);
x_12 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_7, 1, x_13);
lean_ctor_set(x_3, 1, x_4);
{
lean_object* _tmp_2 = x_9;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_1);
x_19 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_17, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_21);
{
lean_object* _tmp_2 = x_15;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_27 = x_23;
} else {
 lean_dec_ref(x_23);
 x_27 = lean_box(0);
}
x_28 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_1);
x_29 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_26, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
if (lean_is_scalar(x_27)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_27;
}
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_4);
x_3 = x_24;
x_4 = x_32;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Elab_Command_tmpIndParam;
x_4 = lean_level_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 1);
x_12 = l_Lean_Expr_ReplaceLevelImpl_initCache;
x_13 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_9, x_2, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_ctor_set(x_7, 1, x_14);
lean_ctor_set(x_3, 1, x_4);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = l_Lean_Expr_ReplaceLevelImpl_initCache;
x_19 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_9, x_2, x_17, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_21);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
lean_inc(x_1);
x_25 = lean_alloc_closure((void*)(l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_25, 0, x_1);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_28 = x_23;
} else {
 lean_dec_ref(x_23);
 x_28 = lean_box(0);
}
x_29 = l_Lean_Expr_ReplaceLevelImpl_initCache;
x_30 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_25, x_2, x_27, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
if (lean_is_scalar(x_28)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_28;
}
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_4);
x_3 = x_24;
x_4 = x_33;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_6, 2);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = 8192;
x_13 = l_Lean_Expr_ReplaceLevelImpl_initCache;
x_14 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_11, x_12, x_9, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
lean_inc(x_1);
x_17 = l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2(x_1, x_12, x_10, x_16);
lean_ctor_set(x_6, 2, x_17);
lean_ctor_set(x_6, 1, x_15);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 2);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
lean_inc(x_1);
x_23 = lean_alloc_closure((void*)(l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_23, 0, x_1);
x_24 = 8192;
x_25 = l_Lean_Expr_ReplaceLevelImpl_initCache;
x_26 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_23, x_24, x_21, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
lean_inc(x_1);
x_29 = l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2(x_1, x_24, x_22, x_28);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_30);
{
lean_object* _tmp_1 = x_19;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_2);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 2);
lean_inc(x_36);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 x_37 = x_32;
} else {
 lean_dec_ref(x_32);
 x_37 = lean_box(0);
}
lean_inc(x_1);
x_38 = lean_alloc_closure((void*)(l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_38, 0, x_1);
x_39 = 8192;
x_40 = l_Lean_Expr_ReplaceLevelImpl_initCache;
x_41 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_38, x_39, x_35, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_box(0);
lean_inc(x_1);
x_44 = l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2(x_1, x_39, x_36, x_43);
if (lean_is_scalar(x_37)) {
 x_45 = lean_alloc_ctor(0, 3, 0);
} else {
 x_45 = x_37;
}
lean_ctor_set(x_45, 0, x_34);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_3);
x_2 = x_33;
x_3 = x_46;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Elab_Command_mkResultUniverse(x_1, x_2);
x_13 = lean_box(0);
x_14 = l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__3(x_12, x_3, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("updateResultingUniverse us: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", r: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", rOffset: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__4;
x_44 = lean_st_ref_get(x_11, x_15);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 3);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get_uint8(x_46, sizeof(void*)*1);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = 0;
x_17 = x_49;
x_18 = x_48;
goto block_43;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_dec(x_44);
x_51 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_unbox(x_52);
lean_dec(x_52);
x_17 = x_54;
x_18 = x_53;
goto block_43;
}
block_43:
{
if (x_17 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1(x_14, x_2, x_4, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_inc(x_14);
x_21 = lean_array_to_list(lean_box(0), x_14);
x_22 = lean_box(0);
x_23 = l_List_mapTRAux___at_Lean_Meta_Match_mkMatcher___spec__6(x_21, x_22);
x_24 = l_Lean_MessageData_ofList(x_23);
lean_dec(x_23);
x_25 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__2;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__4;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_1);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__6;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_2);
x_33 = l_Nat_repr(x_2);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
x_37 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__6;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_16, x_38, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1(x_14, x_2, x_4, x_40, x_6, x_7, x_8, x_9, x_10, x_11, x_41);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_40);
lean_dec(x_2);
return x_42;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_13);
if (x_55 == 0)
{
return x_13;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_13, 0);
x_57 = lean_ctor_get(x_13, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_13);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Level_getOffsetAux(x_11, x_13);
x_15 = l_Lean_Level_getLevelOffset(x_11);
lean_dec(x_11);
x_16 = l_Lean_Level_isParam(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_Command_accLevelAtCtor___closed__2;
x_18 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2(x_15, x_14, x_1, x_2, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bootstrap");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inductiveCheckResultingUniverse");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__2;
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("by default the `inductive/structure commands report an error if the resulting universe is not zero, but may be zero for some universe parameters. Reason: unless this type is a subsingleton, it is hardly what the user wants since it can only eliminate into `Prop`. In the `Init` package, we define subsingletons, and we use this option to disable the check. This option may be deleted in the future after we improve the validator");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__1;
x_3 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__5;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__4;
x_3 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__6;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_bootstrap_inductiveCheckResultingUniverse___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkResultingUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid universe polymorphic type, the resultant universe is not Prop (i.e., 0), but it may be Prop for some parameter values (solution: use 'u+1' or 'max 1 u'");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkResultingUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkResultingUniverse___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkResultingUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_Elab_Command_bootstrap_inductiveCheckResultingUniverse;
x_11 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVars___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_Level_isZero(x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Level_isNeverZero(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_14);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_16);
x_21 = l_Lean_indentD(x_20);
x_22 = l_Lean_Elab_Command_checkResultingUniverse___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__6;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_16);
lean_dec(x_2);
x_27 = lean_box(0);
lean_ctor_set(x_14, 0, x_27);
return x_14;
}
}
else
{
lean_object* x_28; 
lean_dec(x_16);
lean_dec(x_2);
x_28 = lean_box(0);
lean_ctor_set(x_14, 0, x_28);
return x_14;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = l_Lean_Level_isZero(x_29);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = l_Lean_Level_isNeverZero(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_29);
x_34 = l_Lean_indentD(x_33);
x_35 = l_Lean_Elab_Command_checkResultingUniverse___closed__2;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__6;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_30);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_29);
lean_dec(x_2);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_30);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_29);
lean_dec(x_2);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_30);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_checkResultingUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_checkResultingUniverse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkResultingUniverses(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Command_checkResultingUniverse(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Elab_Term_collectUsedFVars(x_12, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_1 = x_11;
x_7 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Elab_Term_collectUsedFVars(x_12, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_10, 2);
lean_inc(x_15);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__1(x_15, x_2, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_1 = x_11;
x_7 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused___closed__2;
x_13 = lean_st_mk_ref(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__2(x_2, x_14, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_8, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_14, x_19);
lean_dec(x_14);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Term_removeUnused(x_1, x_21, x_5, x_6, x_7, x_8, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_apply_1(x_3, x_17);
x_19 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_FunBinders_elabFunBinderViews___spec__3___rarg(x_15, x_16, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = 0;
x_19 = 1;
lean_inc(x_5);
lean_inc(x_1);
x_20 = l_Lean_Meta_mkForallFVars(x_1, x_17, x_18, x_19, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set(x_13, 1, x_21);
x_23 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_2, 1, x_25);
lean_ctor_set(x_23, 0, x_2);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_2, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_free_object(x_2);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_free_object(x_13);
lean_dec(x_16);
lean_free_object(x_2);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_2, 1);
x_38 = lean_ctor_get(x_13, 0);
x_39 = lean_ctor_get(x_13, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_13);
x_40 = 0;
x_41 = 1;
lean_inc(x_5);
lean_inc(x_1);
x_42 = l_Lean_Meta_mkForallFVars(x_1, x_39, x_40, x_41, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1(x_1, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
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
lean_ctor_set(x_2, 1, x_47);
lean_ctor_set(x_2, 0, x_45);
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_45);
lean_free_object(x_2);
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_53 = x_46;
} else {
 lean_dec_ref(x_46);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_38);
lean_free_object(x_2);
lean_dec(x_37);
lean_dec(x_5);
lean_dec(x_1);
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
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_2, 0);
x_60 = lean_ctor_get(x_2, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_2);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_63 = x_59;
} else {
 lean_dec_ref(x_59);
 x_63 = lean_box(0);
}
x_64 = 0;
x_65 = 1;
lean_inc(x_5);
lean_inc(x_1);
x_66 = l_Lean_Meta_mkForallFVars(x_1, x_62, x_64, x_65, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
if (lean_is_scalar(x_63)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_63;
}
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_67);
x_70 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1(x_1, x_60, x_3, x_4, x_5, x_6, x_7, x_8, x_68);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_71);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_69);
x_76 = lean_ctor_get(x_70, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_78 = x_70;
} else {
 lean_dec_ref(x_70);
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
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_5);
lean_dec(x_1);
x_80 = lean_ctor_get(x_66, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_66, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_82 = x_66;
} else {
 lean_dec_ref(x_66);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_13, 2);
x_19 = 0;
x_20 = 1;
lean_inc(x_5);
lean_inc(x_1);
x_21 = l_Lean_Meta_mkForallFVars(x_1, x_17, x_19, x_20, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_5);
lean_inc(x_1);
x_24 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_ctor_set(x_13, 2, x_25);
lean_ctor_set(x_13, 1, x_22);
x_27 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_ctor_set(x_2, 1, x_29);
lean_ctor_set(x_27, 0, x_2);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_27);
lean_ctor_set(x_2, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_13);
lean_free_object(x_2);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_22);
lean_free_object(x_13);
lean_dec(x_16);
lean_free_object(x_2);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
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
lean_free_object(x_13);
lean_dec(x_18);
lean_dec(x_16);
lean_free_object(x_2);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_21);
if (x_41 == 0)
{
return x_21;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_21, 0);
x_43 = lean_ctor_get(x_21, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_21);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_2, 1);
x_46 = lean_ctor_get(x_13, 0);
x_47 = lean_ctor_get(x_13, 1);
x_48 = lean_ctor_get(x_13, 2);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_13);
x_49 = 0;
x_50 = 1;
lean_inc(x_5);
lean_inc(x_1);
x_51 = l_Lean_Meta_mkForallFVars(x_1, x_47, x_49, x_50, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_5);
lean_inc(x_1);
x_54 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1(x_1, x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_46);
lean_ctor_set(x_57, 1, x_52);
lean_ctor_set(x_57, 2, x_55);
x_58 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2(x_1, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
lean_ctor_set(x_2, 1, x_59);
lean_ctor_set(x_2, 0, x_57);
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_2);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
lean_free_object(x_2);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_65 = x_58;
} else {
 lean_dec_ref(x_58);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_52);
lean_dec(x_46);
lean_free_object(x_2);
lean_dec(x_45);
lean_dec(x_5);
lean_dec(x_1);
x_67 = lean_ctor_get(x_54, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_54, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_69 = x_54;
} else {
 lean_dec_ref(x_54);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_48);
lean_dec(x_46);
lean_free_object(x_2);
lean_dec(x_45);
lean_dec(x_5);
lean_dec(x_1);
x_71 = lean_ctor_get(x_51, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_51, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_73 = x_51;
} else {
 lean_dec_ref(x_51);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; lean_object* x_83; 
x_75 = lean_ctor_get(x_2, 0);
x_76 = lean_ctor_get(x_2, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_2);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_75, 2);
lean_inc(x_79);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 x_80 = x_75;
} else {
 lean_dec_ref(x_75);
 x_80 = lean_box(0);
}
x_81 = 0;
x_82 = 1;
lean_inc(x_5);
lean_inc(x_1);
x_83 = l_Lean_Meta_mkForallFVars(x_1, x_78, x_81, x_82, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
lean_inc(x_5);
lean_inc(x_1);
x_86 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1(x_1, x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
if (lean_is_scalar(x_80)) {
 x_89 = lean_alloc_ctor(0, 3, 0);
} else {
 x_89 = x_80;
}
lean_ctor_set(x_89, 0, x_77);
lean_ctor_set(x_89, 1, x_84);
lean_ctor_set(x_89, 2, x_87);
x_90 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2(x_1, x_76, x_3, x_4, x_5, x_6, x_7, x_8, x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
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
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_91);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_89);
x_96 = lean_ctor_get(x_90, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_90, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_98 = x_90;
} else {
 lean_dec_ref(x_90);
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
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_84);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_5);
lean_dec(x_1);
x_100 = lean_ctor_get(x_86, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_86, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_102 = x_86;
} else {
 lean_dec_ref(x_86);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_5);
lean_dec(x_1);
x_104 = lean_ctor_get(x_83, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_83, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_106 = x_83;
} else {
 lean_dec_ref(x_83);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_CollectLevelParams_main(x_5, x_2);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = l_Lean_CollectLevelParams_main(x_5, x_2);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_List_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive___spec__1(x_7, x_6);
x_1 = x_4;
x_2 = x_8;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused___closed__1;
x_2 = l_Lean_Elab_Command_instInhabitedCtorView___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive___closed__1;
x_3 = l_List_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive___spec__2(x_1, x_2);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_nat_dec_le(x_8, x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
x_14 = l_Lean_Elab_Command_instInhabitedInductiveView;
x_15 = lean_array_get(x_14, x_1, x_6);
x_16 = l_Lean_instInhabitedExpr;
x_17 = lean_array_get(x_16, x_2, x_6);
x_18 = lean_ctor_get(x_15, 3);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_3);
x_19 = l_Lean_mkConst(x_18, x_3);
x_20 = l_Lean_Expr_instBEqExpr;
x_21 = l_Lean_Expr_instHashableExpr;
x_22 = l_Std_HashMap_insert___rarg(x_20, x_21, x_7, x_17, x_19);
x_23 = lean_ctor_get(x_4, 2);
x_24 = lean_nat_add(x_6, x_23);
lean_dec(x_6);
x_5 = x_13;
x_6 = x_24;
x_7 = x_22;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_box(0);
x_5 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_3, x_4);
x_6 = lean_array_get_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_unsigned_to_nat(1u);
lean_inc(x_6);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_8);
x_10 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___closed__1;
x_11 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___spec__1(x_1, x_2, x_5, x_9, x_6, x_7, x_10);
lean_dec(x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_216; lean_object* x_217; size_t x_218; uint8_t x_219; 
x_7 = lean_ptr_addr(x_5);
x_8 = x_4 == 0 ? x_7 : x_7 % x_4;
x_216 = lean_ctor_get(x_6, 0);
lean_inc(x_216);
x_217 = lean_array_uget(x_216, x_8);
lean_dec(x_216);
x_218 = lean_ptr_addr(x_217);
lean_dec(x_217);
x_219 = x_218 == x_7;
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = l_Lean_Expr_isFVar(x_5);
if (x_220 == 0)
{
lean_object* x_221; 
x_221 = lean_box(0);
x_9 = x_221;
goto block_215;
}
else
{
lean_object* x_222; 
lean_inc(x_5);
lean_inc(x_2);
x_222 = l_Std_HashMapImp_find_x3f___at_Lean_Meta_reduce_visit___spec__1(x_2, x_5);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; 
x_223 = lean_box(0);
x_9 = x_223;
goto block_215;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
lean_dec(x_2);
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_unsigned_to_nat(0u);
x_226 = l_Array_extract___rarg(x_3, x_225, x_1);
x_227 = l_Lean_mkAppN(x_224, x_226);
x_228 = !lean_is_exclusive(x_6);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_229 = lean_ctor_get(x_6, 0);
x_230 = lean_ctor_get(x_6, 1);
x_231 = lean_array_uset(x_229, x_8, x_5);
lean_inc(x_227);
x_232 = lean_array_uset(x_230, x_8, x_227);
lean_ctor_set(x_6, 1, x_232);
lean_ctor_set(x_6, 0, x_231);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_227);
lean_ctor_set(x_233, 1, x_6);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_234 = lean_ctor_get(x_6, 0);
x_235 = lean_ctor_get(x_6, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_6);
x_236 = lean_array_uset(x_234, x_8, x_5);
lean_inc(x_227);
x_237 = lean_array_uset(x_235, x_8, x_227);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_227);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_240 = lean_ctor_get(x_6, 1);
lean_inc(x_240);
x_241 = lean_array_uget(x_240, x_8);
lean_dec(x_240);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_6);
return x_242;
}
block_215:
{
lean_dec(x_9);
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_10, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
x_16 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_11, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_11);
lean_ctor_set_uint64(x_20, sizeof(void*)*2, x_12);
x_21 = lean_expr_update_app(x_20, x_14, x_18);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
x_25 = lean_array_uset(x_23, x_8, x_5);
lean_inc(x_21);
x_26 = lean_array_uset(x_24, x_8, x_21);
lean_ctor_set(x_19, 1, x_26);
lean_ctor_set(x_19, 0, x_25);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_array_uset(x_27, x_8, x_5);
lean_inc(x_21);
x_30 = lean_array_uset(x_28, x_8, x_21);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_16, 1, x_31);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set_uint64(x_34, sizeof(void*)*2, x_12);
x_35 = lean_expr_update_app(x_34, x_14, x_32);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_38 = x_33;
} else {
 lean_dec_ref(x_33);
 x_38 = lean_box(0);
}
x_39 = lean_array_uset(x_36, x_8, x_5);
lean_inc(x_35);
x_40 = lean_array_uset(x_37, x_8, x_35);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
case 6:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_43 = lean_ctor_get(x_5, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_5, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_5, 2);
lean_inc(x_45);
x_46 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_44);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_47 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_44, x_6);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_45);
x_50 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_45, x_49);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
x_54 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_44);
lean_ctor_set(x_54, 2, x_45);
lean_ctor_set_uint64(x_54, sizeof(void*)*3, x_46);
x_55 = (uint8_t)((x_46 << 24) >> 61);
x_56 = lean_expr_update_lambda(x_54, x_55, x_48, x_52);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_53, 0);
x_59 = lean_ctor_get(x_53, 1);
x_60 = lean_array_uset(x_58, x_8, x_5);
lean_inc(x_56);
x_61 = lean_array_uset(x_59, x_8, x_56);
lean_ctor_set(x_53, 1, x_61);
lean_ctor_set(x_53, 0, x_60);
lean_ctor_set(x_50, 0, x_56);
return x_50;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_53, 0);
x_63 = lean_ctor_get(x_53, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_53);
x_64 = lean_array_uset(x_62, x_8, x_5);
lean_inc(x_56);
x_65 = lean_array_uset(x_63, x_8, x_56);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_50, 1, x_66);
lean_ctor_set(x_50, 0, x_56);
return x_50;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_67 = lean_ctor_get(x_50, 0);
x_68 = lean_ctor_get(x_50, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_50);
x_69 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_69, 0, x_43);
lean_ctor_set(x_69, 1, x_44);
lean_ctor_set(x_69, 2, x_45);
lean_ctor_set_uint64(x_69, sizeof(void*)*3, x_46);
x_70 = (uint8_t)((x_46 << 24) >> 61);
x_71 = lean_expr_update_lambda(x_69, x_70, x_48, x_67);
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_74 = x_68;
} else {
 lean_dec_ref(x_68);
 x_74 = lean_box(0);
}
x_75 = lean_array_uset(x_72, x_8, x_5);
lean_inc(x_71);
x_76 = lean_array_uset(x_73, x_8, x_71);
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_74;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
case 7:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint64_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_79 = lean_ctor_get(x_5, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_5, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_5, 2);
lean_inc(x_81);
x_82 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_80);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_83 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_80, x_6);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
lean_inc(x_81);
x_86 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_81, x_85);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; uint8_t x_93; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = lean_ctor_get(x_86, 1);
x_90 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_90, 0, x_79);
lean_ctor_set(x_90, 1, x_80);
lean_ctor_set(x_90, 2, x_81);
lean_ctor_set_uint64(x_90, sizeof(void*)*3, x_82);
x_91 = (uint8_t)((x_82 << 24) >> 61);
x_92 = lean_expr_update_forall(x_90, x_91, x_84, x_88);
x_93 = !lean_is_exclusive(x_89);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_89, 0);
x_95 = lean_ctor_get(x_89, 1);
x_96 = lean_array_uset(x_94, x_8, x_5);
lean_inc(x_92);
x_97 = lean_array_uset(x_95, x_8, x_92);
lean_ctor_set(x_89, 1, x_97);
lean_ctor_set(x_89, 0, x_96);
lean_ctor_set(x_86, 0, x_92);
return x_86;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_89, 0);
x_99 = lean_ctor_get(x_89, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_89);
x_100 = lean_array_uset(x_98, x_8, x_5);
lean_inc(x_92);
x_101 = lean_array_uset(x_99, x_8, x_92);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_86, 1, x_102);
lean_ctor_set(x_86, 0, x_92);
return x_86;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_103 = lean_ctor_get(x_86, 0);
x_104 = lean_ctor_get(x_86, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_86);
x_105 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_105, 0, x_79);
lean_ctor_set(x_105, 1, x_80);
lean_ctor_set(x_105, 2, x_81);
lean_ctor_set_uint64(x_105, sizeof(void*)*3, x_82);
x_106 = (uint8_t)((x_82 << 24) >> 61);
x_107 = lean_expr_update_forall(x_105, x_106, x_84, x_103);
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_110 = x_104;
} else {
 lean_dec_ref(x_104);
 x_110 = lean_box(0);
}
x_111 = lean_array_uset(x_108, x_8, x_5);
lean_inc(x_107);
x_112 = lean_array_uset(x_109, x_8, x_107);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_107);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
case 8:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint64_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_115 = lean_ctor_get(x_5, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_5, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_5, 2);
lean_inc(x_117);
x_118 = lean_ctor_get(x_5, 3);
lean_inc(x_118);
x_119 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
lean_inc(x_116);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_120 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_116, x_6);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
lean_inc(x_117);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_123 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_117, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
lean_inc(x_118);
x_126 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_118, x_125);
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_126, 0);
x_129 = lean_ctor_get(x_126, 1);
x_130 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_130, 0, x_115);
lean_ctor_set(x_130, 1, x_116);
lean_ctor_set(x_130, 2, x_117);
lean_ctor_set(x_130, 3, x_118);
lean_ctor_set_uint64(x_130, sizeof(void*)*4, x_119);
x_131 = lean_expr_update_let(x_130, x_121, x_124, x_128);
x_132 = !lean_is_exclusive(x_129);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_129, 0);
x_134 = lean_ctor_get(x_129, 1);
x_135 = lean_array_uset(x_133, x_8, x_5);
lean_inc(x_131);
x_136 = lean_array_uset(x_134, x_8, x_131);
lean_ctor_set(x_129, 1, x_136);
lean_ctor_set(x_129, 0, x_135);
lean_ctor_set(x_126, 0, x_131);
return x_126;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_ctor_get(x_129, 0);
x_138 = lean_ctor_get(x_129, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_129);
x_139 = lean_array_uset(x_137, x_8, x_5);
lean_inc(x_131);
x_140 = lean_array_uset(x_138, x_8, x_131);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_126, 1, x_141);
lean_ctor_set(x_126, 0, x_131);
return x_126;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_142 = lean_ctor_get(x_126, 0);
x_143 = lean_ctor_get(x_126, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_126);
x_144 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_144, 0, x_115);
lean_ctor_set(x_144, 1, x_116);
lean_ctor_set(x_144, 2, x_117);
lean_ctor_set(x_144, 3, x_118);
lean_ctor_set_uint64(x_144, sizeof(void*)*4, x_119);
x_145 = lean_expr_update_let(x_144, x_121, x_124, x_142);
x_146 = lean_ctor_get(x_143, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_148 = x_143;
} else {
 lean_dec_ref(x_143);
 x_148 = lean_box(0);
}
x_149 = lean_array_uset(x_146, x_8, x_5);
lean_inc(x_145);
x_150 = lean_array_uset(x_147, x_8, x_145);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_145);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
case 10:
{
lean_object* x_153; lean_object* x_154; uint64_t x_155; lean_object* x_156; uint8_t x_157; 
x_153 = lean_ctor_get(x_5, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_5, 1);
lean_inc(x_154);
x_155 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_154);
x_156 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_154, x_6);
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_158 = lean_ctor_get(x_156, 0);
x_159 = lean_ctor_get(x_156, 1);
x_160 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_160, 0, x_153);
lean_ctor_set(x_160, 1, x_154);
lean_ctor_set_uint64(x_160, sizeof(void*)*2, x_155);
x_161 = lean_expr_update_mdata(x_160, x_158);
x_162 = !lean_is_exclusive(x_159);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_159, 0);
x_164 = lean_ctor_get(x_159, 1);
x_165 = lean_array_uset(x_163, x_8, x_5);
lean_inc(x_161);
x_166 = lean_array_uset(x_164, x_8, x_161);
lean_ctor_set(x_159, 1, x_166);
lean_ctor_set(x_159, 0, x_165);
lean_ctor_set(x_156, 0, x_161);
return x_156;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_167 = lean_ctor_get(x_159, 0);
x_168 = lean_ctor_get(x_159, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_159);
x_169 = lean_array_uset(x_167, x_8, x_5);
lean_inc(x_161);
x_170 = lean_array_uset(x_168, x_8, x_161);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
lean_ctor_set(x_156, 1, x_171);
lean_ctor_set(x_156, 0, x_161);
return x_156;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_172 = lean_ctor_get(x_156, 0);
x_173 = lean_ctor_get(x_156, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_156);
x_174 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_174, 0, x_153);
lean_ctor_set(x_174, 1, x_154);
lean_ctor_set_uint64(x_174, sizeof(void*)*2, x_155);
x_175 = lean_expr_update_mdata(x_174, x_172);
x_176 = lean_ctor_get(x_173, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_173, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_178 = x_173;
} else {
 lean_dec_ref(x_173);
 x_178 = lean_box(0);
}
x_179 = lean_array_uset(x_176, x_8, x_5);
lean_inc(x_175);
x_180 = lean_array_uset(x_177, x_8, x_175);
if (lean_is_scalar(x_178)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_178;
}
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_175);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
case 11:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; uint64_t x_186; lean_object* x_187; uint8_t x_188; 
x_183 = lean_ctor_get(x_5, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_5, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_5, 2);
lean_inc(x_185);
x_186 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_185);
x_187 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_185, x_6);
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_189 = lean_ctor_get(x_187, 0);
x_190 = lean_ctor_get(x_187, 1);
x_191 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_191, 0, x_183);
lean_ctor_set(x_191, 1, x_184);
lean_ctor_set(x_191, 2, x_185);
lean_ctor_set_uint64(x_191, sizeof(void*)*3, x_186);
x_192 = lean_expr_update_proj(x_191, x_189);
x_193 = !lean_is_exclusive(x_190);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_ctor_get(x_190, 0);
x_195 = lean_ctor_get(x_190, 1);
x_196 = lean_array_uset(x_194, x_8, x_5);
lean_inc(x_192);
x_197 = lean_array_uset(x_195, x_8, x_192);
lean_ctor_set(x_190, 1, x_197);
lean_ctor_set(x_190, 0, x_196);
lean_ctor_set(x_187, 0, x_192);
return x_187;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_198 = lean_ctor_get(x_190, 0);
x_199 = lean_ctor_get(x_190, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_190);
x_200 = lean_array_uset(x_198, x_8, x_5);
lean_inc(x_192);
x_201 = lean_array_uset(x_199, x_8, x_192);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
lean_ctor_set(x_187, 1, x_202);
lean_ctor_set(x_187, 0, x_192);
return x_187;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_203 = lean_ctor_get(x_187, 0);
x_204 = lean_ctor_get(x_187, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_187);
x_205 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_205, 0, x_183);
lean_ctor_set(x_205, 1, x_184);
lean_ctor_set(x_205, 2, x_185);
lean_ctor_set_uint64(x_205, sizeof(void*)*3, x_186);
x_206 = lean_expr_update_proj(x_205, x_203);
x_207 = lean_ctor_get(x_204, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_204, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_209 = x_204;
} else {
 lean_dec_ref(x_204);
 x_209 = lean_box(0);
}
x_210 = lean_array_uset(x_207, x_8, x_5);
lean_inc(x_206);
x_211 = lean_array_uset(x_208, x_8, x_206);
if (lean_is_scalar(x_209)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_209;
}
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_206);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
default: 
{
lean_object* x_214; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_5);
lean_ctor_set(x_214, 1, x_6);
return x_214;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_12 = 8192;
x_13 = l_Lean_Expr_ReplaceImpl_initCache;
lean_inc(x_3);
x_14 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_12, x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = 0;
x_17 = 1;
x_18 = l_Lean_Meta_mkForallFVars(x_3, x_15, x_16, x_17, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_2);
lean_inc(x_3);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2___lambda__1___boxed), 11, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(x_19, x_20, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_ctor_set(x_15, 1, x_23);
x_25 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2(x_1, x_2, x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_4, 1, x_27);
lean_ctor_set(x_25, 0, x_4);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_4, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_15);
lean_free_object(x_4);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
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
lean_free_object(x_15);
lean_dec(x_18);
lean_free_object(x_4);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_4, 1);
x_40 = lean_ctor_get(x_15, 0);
x_41 = lean_ctor_get(x_15, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_15);
lean_inc(x_2);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_2);
lean_inc(x_3);
lean_inc(x_1);
x_43 = lean_alloc_closure((void*)(l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2___lambda__1___boxed), 11, 2);
lean_closure_set(x_43, 0, x_1);
lean_closure_set(x_43, 1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_44 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(x_41, x_42, x_43, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2(x_1, x_2, x_3, x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
lean_ctor_set(x_4, 1, x_49);
lean_ctor_set(x_4, 0, x_47);
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_4);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_47);
lean_free_object(x_4);
x_53 = lean_ctor_get(x_48, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_55 = x_48;
} else {
 lean_dec_ref(x_48);
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
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_40);
lean_free_object(x_4);
lean_dec(x_39);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_ctor_get(x_44, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_44, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_59 = x_44;
} else {
 lean_dec_ref(x_44);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_4, 0);
x_62 = lean_ctor_get(x_4, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_4);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_65 = x_61;
} else {
 lean_dec_ref(x_61);
 x_65 = lean_box(0);
}
lean_inc(x_2);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_2);
lean_inc(x_3);
lean_inc(x_1);
x_67 = lean_alloc_closure((void*)(l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2___lambda__1___boxed), 11, 2);
lean_closure_set(x_67, 0, x_1);
lean_closure_set(x_67, 1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_68 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(x_64, x_66, x_67, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
if (lean_is_scalar(x_65)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_65;
}
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2(x_1, x_2, x_3, x_62, x_5, x_6, x_7, x_8, x_9, x_10, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_73);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = lean_ctor_get(x_68, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_68, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_84 = x_68;
} else {
 lean_dec_ref(x_68);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_ctor_get(x_15, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2(x_1, x_2, x_3, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set(x_15, 2, x_22);
x_24 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__3(x_1, x_2, x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_ctor_set(x_4, 1, x_26);
lean_ctor_set(x_24, 0, x_4);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_24);
lean_ctor_set(x_4, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_15);
lean_free_object(x_4);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
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
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_4);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_4, 1);
x_39 = lean_ctor_get(x_15, 0);
x_40 = lean_ctor_get(x_15, 1);
x_41 = lean_ctor_get(x_15, 2);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_42 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2(x_1, x_2, x_3, x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_40);
lean_ctor_set(x_45, 2, x_43);
x_46 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__3(x_1, x_2, x_3, x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
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
lean_ctor_set(x_4, 1, x_47);
lean_ctor_set(x_4, 0, x_45);
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_4);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_45);
lean_free_object(x_4);
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_53 = x_46;
} else {
 lean_dec_ref(x_46);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_4);
lean_dec(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_4, 0);
x_60 = lean_ctor_get(x_4, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_4);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 2);
lean_inc(x_63);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 x_64 = x_59;
} else {
 lean_dec_ref(x_59);
 x_64 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_65 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2(x_1, x_2, x_3, x_63, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
if (lean_is_scalar(x_64)) {
 x_68 = lean_alloc_ctor(0, 3, 0);
} else {
 x_68 = x_64;
}
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_62);
lean_ctor_set(x_68, 2, x_66);
x_69 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__3(x_1, x_2, x_3, x_60, x_5, x_6, x_7, x_8, x_9, x_10, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_70);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_68);
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_77 = x_69;
} else {
 lean_dec_ref(x_69);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = lean_ctor_get(x_65, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_65, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_81 = x_65;
} else {
 lean_dec_ref(x_65);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__3(x_4, x_5, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_6 = lean_array_uget(x_1, x_3);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*5);
lean_dec(x_6);
x_9 = l_Lean_Name_instBEqName;
x_10 = l_Lean_instHashableName;
x_11 = lean_box(x_8);
x_12 = l_Std_HashMap_insert___rarg(x_9, x_10, x_4, x_7, x_11);
x_13 = 1;
x_14 = x_3 + x_13;
x_3 = x_14;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_6 = lean_array_uget(x_1, x_3);
x_7 = lean_ctor_get(x_6, 7);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_array_get_size(x_7);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__1(x_7, x_9, x_10, x_4);
lean_dec(x_7);
x_12 = 1;
x_13 = x_3 + x_12;
x_3 = x_13;
x_4 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_4 = 0;
x_5 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___closed__1;
x_6 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__2(x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Std.Data.HashMap");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Std.HashMap.find!");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("key is not in the map");
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__1;
x_2 = l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(177u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_2);
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_hasOutParams___spec__2(x_2, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = l_instInhabitedBool;
x_14 = l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__4;
x_15 = lean_box(x_13);
x_16 = lean_panic_fn(x_15, x_14);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; 
x_18 = 1;
x_19 = l_Lean_Expr_inferImplicit(x_11, x_1, x_18);
lean_ctor_set(x_7, 1, x_19);
lean_ctor_set(x_3, 1, x_4);
{
lean_object* _tmp_2 = x_9;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
uint8_t x_21; lean_object* x_22; 
x_21 = 0;
x_22 = l_Lean_Expr_inferImplicit(x_11, x_1, x_21);
lean_ctor_set(x_7, 1, x_22);
lean_ctor_set(x_3, 1, x_4);
{
lean_object* _tmp_2 = x_9;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; 
x_26 = 1;
x_27 = l_Lean_Expr_inferImplicit(x_11, x_1, x_26);
lean_ctor_set(x_7, 1, x_27);
lean_ctor_set(x_3, 1, x_4);
{
lean_object* _tmp_2 = x_9;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
uint8_t x_29; lean_object* x_30; 
x_29 = 0;
x_30 = l_Lean_Expr_inferImplicit(x_11, x_1, x_29);
lean_ctor_set(x_7, 1, x_30);
lean_ctor_set(x_3, 1, x_4);
{
lean_object* _tmp_2 = x_9;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_3, 1);
x_33 = lean_ctor_get(x_7, 0);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_7);
lean_inc(x_33);
lean_inc(x_2);
x_35 = l_Std_HashMapImp_find_x3f___at_Lean_hasOutParams___spec__2(x_2, x_33);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = l_instInhabitedBool;
x_37 = l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__4;
x_38 = lean_box(x_36);
x_39 = lean_panic_fn(x_38, x_37);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_41 = 1;
x_42 = l_Lean_Expr_inferImplicit(x_34, x_1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_43);
{
lean_object* _tmp_2 = x_32;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_45 = 0;
x_46 = l_Lean_Expr_inferImplicit(x_34, x_1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_33);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_47);
{
lean_object* _tmp_2 = x_32;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_35, 0);
lean_inc(x_49);
lean_dec(x_35);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_51 = 1;
x_52 = l_Lean_Expr_inferImplicit(x_34, x_1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_33);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_53);
{
lean_object* _tmp_2 = x_32;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_55 = 0;
x_56 = l_Lean_Expr_inferImplicit(x_34, x_1, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_33);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_57);
{
lean_object* _tmp_2 = x_32;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_3, 0);
x_60 = lean_ctor_get(x_3, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_3);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_63 = x_59;
} else {
 lean_dec_ref(x_59);
 x_63 = lean_box(0);
}
lean_inc(x_61);
lean_inc(x_2);
x_64 = l_Std_HashMapImp_find_x3f___at_Lean_hasOutParams___spec__2(x_2, x_61);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = l_instInhabitedBool;
x_66 = l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__4;
x_67 = lean_box(x_65);
x_68 = lean_panic_fn(x_67, x_66);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = 1;
x_71 = l_Lean_Expr_inferImplicit(x_62, x_1, x_70);
if (lean_is_scalar(x_63)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_63;
}
lean_ctor_set(x_72, 0, x_61);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_4);
x_3 = x_60;
x_4 = x_73;
goto _start;
}
else
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = 0;
x_76 = l_Lean_Expr_inferImplicit(x_62, x_1, x_75);
if (lean_is_scalar(x_63)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_63;
}
lean_ctor_set(x_77, 0, x_61);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_4);
x_3 = x_60;
x_4 = x_78;
goto _start;
}
}
else
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_64, 0);
lean_inc(x_80);
lean_dec(x_64);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = 1;
x_83 = l_Lean_Expr_inferImplicit(x_62, x_1, x_82);
if (lean_is_scalar(x_63)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_63;
}
lean_ctor_set(x_84, 0, x_61);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_4);
x_3 = x_60;
x_4 = x_85;
goto _start;
}
else
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = 0;
x_88 = l_Lean_Expr_inferImplicit(x_62, x_1, x_87);
if (lean_is_scalar(x_63)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_63;
}
lean_ctor_set(x_89, 0, x_61);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_4);
x_3 = x_60;
x_4 = x_90;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_7, 2);
x_11 = lean_box(0);
lean_inc(x_2);
x_12 = l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1(x_1, x_2, x_10, x_11);
lean_ctor_set(x_7, 2, x_12);
lean_ctor_set(x_3, 1, x_4);
{
lean_object* _tmp_2 = x_9;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_7, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_18 = lean_box(0);
lean_inc(x_2);
x_19 = l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1(x_1, x_2, x_17, x_18);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_20);
{
lean_object* _tmp_2 = x_14;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 2);
lean_inc(x_26);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 x_27 = x_22;
} else {
 lean_dec_ref(x_22);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
lean_inc(x_2);
x_29 = l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1(x_1, x_2, x_26, x_28);
if (lean_is_scalar(x_27)) {
 x_30 = lean_alloc_ctor(0, 3, 0);
} else {
 x_30 = x_27;
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
x_3 = x_23;
x_4 = x_31;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod(x_1);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__2(x_2, x_4, x_3, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_mk_rec_on(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_throwKernelException___at_Lean_Elab_Term_evalExpr___spec__4(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_2);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_take(x_7, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_16);
x_22 = lean_st_ref_set(x_7, x_18, x_19);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_st_ref_set(x_7, x_32, x_19);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_mk_ibelow(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_throwKernelException___at_Lean_Elab_Term_evalExpr___spec__4(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_2);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_take(x_7, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_16);
x_22 = lean_st_ref_set(x_7, x_18, x_19);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_st_ref_set(x_7, x_32, x_19);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_mk_below(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_throwKernelException___at_Lean_Elab_Term_evalExpr___spec__4(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_2);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_take(x_7, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_16);
x_22 = lean_st_ref_set(x_7, x_18, x_19);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_st_ref_set(x_7, x_32, x_19);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_mk_cases_on(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_throwKernelException___at_Lean_Elab_Term_evalExpr___spec__4(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_2);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_take(x_7, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_16);
x_22 = lean_st_ref_set(x_7, x_18, x_19);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_st_ref_set(x_7, x_32, x_19);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_1 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_5);
x_12 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
if (x_2 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_mkIBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__2(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1___closed__1;
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__2(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_dec(x_4);
if (x_1 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
else
{
if (x_2 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
else
{
lean_object* x_16; 
lean_inc(x_9);
lean_inc(x_5);
x_16 = l_Lean_mkBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__3(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1(x_1, x_2, x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_17);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__3(uint8_t x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_dec(x_6);
if (x_1 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__2(x_1, x_2, x_3, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
return x_15;
}
else
{
if (x_4 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__2(x_1, x_2, x_3, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
return x_17;
}
else
{
if (x_5 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__2(x_1, x_2, x_3, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
return x_19;
}
else
{
lean_object* x_20; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_3);
x_20 = l_Lean_mkNoConfusion(x_3, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__2(x_1, x_2, x_3, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5(uint8_t x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = x_7 < x_6;
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
x_18 = lean_array_uget(x_5, x_7);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_13);
lean_inc(x_9);
x_20 = l_Lean_mkRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__1(x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
if (x_3 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_23 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__3(x_3, x_4, x_19, x_1, x_2, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
x_33 = 1;
x_34 = x_7 + x_33;
x_7 = x_34;
x_8 = x_32;
x_15 = x_31;
goto _start;
}
}
else
{
uint8_t x_36; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_dec(x_20);
lean_inc(x_13);
lean_inc(x_9);
x_41 = l_Lean_mkCasesOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__4(x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_44 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__3(x_3, x_4, x_19, x_1, x_2, x_42, x_9, x_10, x_11, x_12, x_13, x_14, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec(x_45);
lean_ctor_set(x_44, 0, x_48);
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_dec(x_44);
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; size_t x_54; size_t x_55; 
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_dec(x_44);
x_53 = lean_ctor_get(x_45, 0);
lean_inc(x_53);
lean_dec(x_45);
x_54 = 1;
x_55 = x_7 + x_54;
x_7 = x_55;
x_8 = x_53;
x_15 = x_52;
goto _start;
}
}
else
{
uint8_t x_57; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_57 = !lean_is_exclusive(x_44);
if (x_57 == 0)
{
return x_44;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_44, 0);
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_44);
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
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_61 = !lean_is_exclusive(x_41);
if (x_61 == 0)
{
return x_41;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_41, 0);
x_63 = lean_ctor_get(x_41, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_41);
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
uint8_t x_65; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_65 = !lean_is_exclusive(x_20);
if (x_65 == 0)
{
return x_20;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_20, 0);
x_67 = lean_ctor_get(x_20, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_20);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBInductionOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_mk_binduction_on(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_throwKernelException___at_Lean_Elab_Term_evalExpr___spec__4(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_2);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_take(x_7, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_16);
x_22 = lean_st_ref_set(x_7, x_18, x_19);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_st_ref_set(x_7, x_32, x_19);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_mk_brec_on(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_throwKernelException___at_Lean_Elab_Term_evalExpr___spec__4(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_2);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_take(x_7, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_16);
x_22 = lean_st_ref_set(x_7, x_18, x_19);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_st_ref_set(x_7, x_32, x_19);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8___lambda__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_1 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_5);
x_12 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
if (x_2 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_mkBInductionOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1___closed__1;
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8(uint8_t x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_5 < x_4;
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_6);
x_16 = lean_array_uget(x_3, x_5);
if (x_1 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
lean_inc(x_11);
lean_inc(x_7);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8___lambda__1(x_1, x_2, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = x_5 + x_23;
x_5 = x_24;
x_6 = x_22;
x_13 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_7);
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
else
{
if (x_2 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 3);
lean_inc(x_30);
lean_dec(x_16);
x_31 = lean_box(0);
lean_inc(x_11);
lean_inc(x_7);
x_32 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8___lambda__1(x_1, x_2, x_30, x_31, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = 1;
x_37 = x_5 + x_36;
x_5 = x_37;
x_6 = x_35;
x_13 = x_34;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_11);
lean_dec(x_7);
x_39 = !lean_is_exclusive(x_32);
if (x_39 == 0)
{
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_32, 0);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_32);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_16, 3);
lean_inc(x_43);
lean_dec(x_16);
lean_inc(x_11);
lean_inc(x_7);
x_44 = l_Lean_mkBRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__7(x_43, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_11);
lean_inc(x_7);
x_47 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8___lambda__1(x_1, x_2, x_43, x_45, x_7, x_8, x_9, x_10, x_11, x_12, x_46);
lean_dec(x_45);
lean_dec(x_43);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = 1;
x_52 = x_5 + x_51;
x_5 = x_52;
x_6 = x_50;
x_13 = x_49;
goto _start;
}
else
{
uint8_t x_54; 
lean_dec(x_11);
lean_dec(x_7);
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_43);
lean_dec(x_11);
lean_dec(x_7);
x_58 = !lean_is_exclusive(x_44);
if (x_58 == 0)
{
return x_44;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_44, 0);
x_60 = lean_ctor_get(x_44, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_44);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Eq");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HEq");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PUnit");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Prod");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__2;
lean_inc(x_12);
x_14 = l_Lean_Environment_contains(x_12, x_13);
x_15 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__4;
lean_inc(x_12);
x_16 = l_Lean_Environment_contains(x_12, x_15);
x_17 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__6;
lean_inc(x_12);
x_18 = l_Lean_Environment_contains(x_12, x_17);
x_19 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__8;
x_20 = l_Lean_Environment_contains(x_12, x_19);
x_21 = lean_array_get_size(x_1);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_25 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5(x_14, x_16, x_18, x_20, x_1, x_22, x_23, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8(x_18, x_20, x_1, x_22, x_23, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_26);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_24);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 0);
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_25);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkIBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkCasesOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__2(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__3(x_14, x_15, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = lean_unbox(x_4);
lean_dec(x_4);
x_20 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_21 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_22 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5(x_16, x_17, x_18, x_19, x_5, x_20, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBInductionOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkBInductionOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkBRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8___lambda__1(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8(x_14, x_15, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_nat_dec_le(x_15, x_6);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_5, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_5, x_19);
lean_dec(x_5);
x_21 = l_Lean_instInhabitedExpr;
x_22 = lean_array_get(x_21, x_3, x_6);
x_23 = l_Lean_Elab_Command_instInhabitedElabHeaderResult;
x_24 = lean_array_get(x_23, x_1, x_6);
x_25 = lean_ctor_get(x_24, 4);
lean_inc(x_25);
x_26 = 0;
x_27 = 1;
lean_inc(x_10);
lean_inc(x_2);
x_28 = l_Lean_Meta_mkForallFVars(x_2, x_25, x_26, x_27, x_10, x_11, x_12, x_13, x_14);
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_24);
lean_inc(x_2);
lean_inc(x_3);
x_31 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors(x_3, x_22, x_2, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_24, 0);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_ctor_get(x_34, 3);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_32);
x_37 = lean_array_push(x_7, x_36);
x_38 = lean_ctor_get(x_4, 2);
x_39 = lean_nat_add(x_6, x_38);
lean_dec(x_6);
x_5 = x_20;
x_6 = x_39;
x_7 = x_37;
x_14 = x_33;
goto _start;
}
else
{
uint8_t x_41; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_31);
if (x_41 == 0)
{
return x_31;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_31, 0);
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_31);
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
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_28);
if (x_45 == 0)
{
return x_28;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_28, 0);
x_47 = lean_ctor_get(x_28, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_28);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_7);
lean_ctor_set(x_49, 1, x_14);
return x_49;
}
}
else
{
lean_object* x_50; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_7);
lean_ctor_set(x_50, 1, x_14);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 < x_2;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_3);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_19 = l_Lean_Elab_Term_applyAttributesAt(x_15, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = 1;
x_22 = x_3 + x_21;
x_23 = lean_box(0);
x_3 = x_22;
x_4 = x_23;
x_11 = x_20;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; 
lean_inc(x_9);
x_17 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive(x_9);
x_18 = l_Lean_Elab_sortDeclLevelParams(x_1, x_2, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_23);
lean_inc(x_3);
x_24 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts(x_3, x_4, x_23, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_6);
lean_inc(x_3);
x_27 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod(x_3, x_6, x_25);
x_28 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_6);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_7);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_28);
x_29 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_28, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
lean_inc(x_14);
lean_inc(x_10);
x_31 = l_Lean_addDecl___at_Lean_Elab_Term_evalExpr___spec__3(x_28, x_10, x_11, x_12, x_13, x_14, x_15, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_33 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions(x_3, x_10, x_11, x_12, x_13, x_14, x_15, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_usize_of_nat(x_8);
x_36 = 0;
x_37 = lean_box(0);
x_38 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__2(x_3, x_35, x_36, x_37, x_10, x_11, x_12, x_13, x_14, x_15, x_34);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_33);
if (x_47 == 0)
{
return x_33;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_33, 0);
x_49 = lean_ctor_get(x_33, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_33);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_31);
if (x_51 == 0)
{
return x_31;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_31, 0);
x_53 = lean_ctor_get(x_31, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_31);
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
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_29);
if (x_55 == 0)
{
return x_29;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_29, 0);
x_57 = lean_ctor_get(x_29, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_29);
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
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
x_59 = !lean_is_exclusive(x_24);
if (x_59 == 0)
{
return x_24;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_24, 0);
x_61 = lean_ctor_get(x_24, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_24);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_array_get_size(x_10);
x_19 = lean_nat_add(x_18, x_1);
lean_dec(x_1);
lean_inc(x_13);
x_20 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2(x_10, x_2, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParam(x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_22);
if (x_9 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_24);
x_26 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkResultingUniverses(x_24, x_11, x_12, x_13, x_14, x_15, x_16, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__1(x_3, x_4, x_5, x_6, x_18, x_19, x_7, x_8, x_24, x_11, x_12, x_13, x_14, x_15, x_16, x_27);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_dec(x_23);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_19);
x_35 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse(x_19, x_33, x_11, x_12, x_13, x_14, x_15, x_16, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__1(x_3, x_4, x_5, x_6, x_18, x_19, x_7, x_8, x_36, x_11, x_12, x_13, x_14, x_15, x_16, x_37);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_20);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_array_get_size(x_7);
x_17 = lean_array_get_size(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_unsigned_to_nat(1u);
lean_inc(x_17);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_19);
x_21 = l_Lean_Elab_Command_instInhabitedCtorView___closed__1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_17);
lean_inc(x_8);
x_22 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__1(x_2, x_7, x_8, x_20, x_17, x_18, x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_to_list(lean_box(0), x_23);
x_26 = 0;
x_27 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_28 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_26, x_26, x_27, x_9, x_10, x_11, x_12, x_13, x_14, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_25);
x_30 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse(x_25, x_9, x_10, x_11, x_12, x_13, x_14, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_9);
x_33 = l_Lean_Elab_Command_shouldInferResultUniverse(x_31, x_9, x_10, x_11, x_12, x_13, x_14, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_box(x_5);
lean_inc(x_25);
x_37 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__2___boxed), 17, 9);
lean_closure_set(x_37, 0, x_16);
lean_closure_set(x_37, 1, x_25);
lean_closure_set(x_37, 2, x_3);
lean_closure_set(x_37, 3, x_4);
lean_closure_set(x_37, 4, x_1);
lean_closure_set(x_37, 5, x_8);
lean_closure_set(x_37, 6, x_36);
lean_closure_set(x_37, 7, x_17);
lean_closure_set(x_37, 8, x_34);
x_38 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed___rarg(x_6, x_25, x_37, x_9, x_10, x_11, x_12, x_13, x_14, x_35);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_33);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
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
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_28);
if (x_47 == 0)
{
return x_28;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_28, 0);
x_49 = lean_ctor_get(x_28, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_28);
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
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_22;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeader(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(x_4);
lean_inc(x_14);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__3___boxed), 15, 6);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_3);
lean_closure_set(x_17, 4, x_16);
lean_closure_set(x_17, 5, x_5);
x_18 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg(x_14, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lean_Elab_Command_instInhabitedInductiveView;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get(x_10, x_2, x_11);
x_13 = l_Lean_Elab_Term_getLevelNames___rarg(x_4, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_3);
x_16 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_12, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*2 + 3);
lean_dec(x_19);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_box(x_20);
lean_inc(x_18);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__4___boxed), 12, 5);
lean_closure_set(x_23, 0, x_2);
lean_closure_set(x_23, 1, x_14);
lean_closure_set(x_23, 2, x_18);
lean_closure_set(x_23, 3, x_22);
lean_closure_set(x_23, 4, x_1);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_7, 3);
x_26 = l_Lean_replaceRef(x_21, x_25);
lean_dec(x_25);
lean_dec(x_21);
lean_ctor_set(x_7, 3, x_26);
x_27 = l_Lean_Elab_Term_withLevelNames___rarg(x_18, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
x_30 = lean_ctor_get(x_7, 2);
x_31 = lean_ctor_get(x_7, 3);
x_32 = lean_ctor_get(x_7, 4);
x_33 = lean_ctor_get(x_7, 5);
x_34 = lean_ctor_get(x_7, 6);
x_35 = lean_ctor_get(x_7, 7);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_7);
x_36 = l_Lean_replaceRef(x_21, x_31);
lean_dec(x_31);
lean_dec(x_21);
x_37 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_29);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set(x_37, 4, x_32);
lean_ctor_set(x_37, 5, x_33);
lean_ctor_set(x_37, 6, x_34);
lean_ctor_set(x_37, 7, x_35);
x_38 = l_Lean_Elab_Term_withLevelNames___rarg(x_18, x_23, x_3, x_4, x_5, x_6, x_37, x_8, x_17);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
return x_16;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_16, 0);
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_16);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_8);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__2___boxed(lean_object** _args) {
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
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = lean_unbox(x_9);
lean_dec(x_9);
x_20 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_18, x_8, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_8);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__3(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__4(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_4 < x_3;
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_array_uget(x_2, x_4);
x_12 = lean_ctor_get(x_11, 8);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
size_t x_16; size_t x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_16 = 1;
x_17 = x_4 + x_16;
x_4 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_13, x_13);
if (x_19 == 0)
{
size_t x_20; size_t x_21; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_20 = 1;
x_21 = x_4 + x_20;
x_4 = x_21;
goto _start;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_25 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__1(x_1, x_12, x_23, x_24);
lean_dec(x_12);
if (x_25 == 0)
{
size_t x_26; size_t x_27; 
lean_dec(x_11);
x_26 = 1;
x_27 = x_4 + x_26;
x_4 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_29 = lean_ctor_get(x_11, 3);
lean_inc(x_29);
lean_dec(x_11);
x_30 = lean_array_push(x_5, x_29);
x_31 = 1;
x_32 = x_4 + x_31;
x_4 = x_32;
x_5 = x_30;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_4 < x_3;
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_uget(x_2, x_4);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = l_Lean_NameSet_contains(x_5, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_box(0);
lean_inc(x_12);
x_15 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_5, x_12, x_14);
x_16 = lean_array_get_size(x_1);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Lean_Elab_Command_instInhabitedCtorView___closed__1;
x_20 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__2(x_12, x_1, x_17, x_18, x_19, x_6, x_7, x_8);
lean_dec(x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_6);
x_23 = l_Lean_Elab_DerivingClassView_applyHandlers(x_11, x_21, x_6, x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = 1;
x_26 = x_4 + x_25;
x_4 = x_26;
x_5 = x_15;
x_8 = x_24;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
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
size_t x_32; size_t x_33; 
lean_dec(x_12);
lean_dec(x_11);
x_32 = 1;
x_33 = x_4 + x_32;
x_4 = x_33;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_4 < x_3;
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_array_uget(x_2, x_4);
x_12 = lean_ctor_get(x_11, 8);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_array_get_size(x_12);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__3(x_1, x_12, x_14, x_15, x_5, x_6, x_7, x_8);
lean_dec(x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = x_4 + x_19;
x_4 = x_20;
x_5 = x_17;
x_8 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = l_Lean_NameSet_empty;
x_9 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__4(x_1, x_1, x_6, x_7, x_8, x_2, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__2(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__3(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___spec__4(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabInductiveViews___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 < x_2;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_3);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_Lean_Meta_mkInjectiveTheorems(x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 1;
x_19 = x_3 + x_18;
x_20 = lean_box(0);
x_3 = x_19;
x_4 = x_20;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInductiveViews___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 3);
x_15 = l_Lean_replaceRef(x_1, x_14);
lean_dec(x_14);
lean_ctor_set(x_10, 3, x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_16 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl(x_2, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
x_18 = l_Lean_Meta_mkSizeOfInstances(x_4, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_20 = l_Lean_Meta_IndPredBelow_mkBelow(x_4, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_array_get_size(x_3);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabInductiveViews___spec__1(x_3, x_23, x_5, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
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
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
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
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_18);
if (x_38 == 0)
{
return x_18;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_18, 0);
x_40 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_18);
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
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_16);
if (x_42 == 0)
{
return x_16;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_16, 0);
x_44 = lean_ctor_get(x_16, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_16);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_46 = lean_ctor_get(x_10, 0);
x_47 = lean_ctor_get(x_10, 1);
x_48 = lean_ctor_get(x_10, 2);
x_49 = lean_ctor_get(x_10, 3);
x_50 = lean_ctor_get(x_10, 4);
x_51 = lean_ctor_get(x_10, 5);
x_52 = lean_ctor_get(x_10, 6);
x_53 = lean_ctor_get(x_10, 7);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_10);
x_54 = l_Lean_replaceRef(x_1, x_49);
lean_dec(x_49);
x_55 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_47);
lean_ctor_set(x_55, 2, x_48);
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 4, x_50);
lean_ctor_set(x_55, 5, x_51);
lean_ctor_set(x_55, 6, x_52);
lean_ctor_set(x_55, 7, x_53);
lean_inc(x_11);
lean_inc(x_55);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_56 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl(x_2, x_3, x_6, x_7, x_8, x_9, x_55, x_11, x_12);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
lean_inc(x_11);
lean_inc(x_55);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
x_58 = l_Lean_Meta_mkSizeOfInstances(x_4, x_8, x_9, x_55, x_11, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
lean_inc(x_11);
lean_inc(x_55);
lean_inc(x_9);
lean_inc(x_8);
x_60 = l_Lean_Meta_IndPredBelow_mkBelow(x_4, x_8, x_9, x_55, x_11, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; size_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_array_get_size(x_3);
x_63 = lean_usize_of_nat(x_62);
lean_dec(x_62);
x_64 = lean_box(0);
x_65 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabInductiveViews___spec__1(x_3, x_63, x_5, x_64, x_6, x_7, x_8, x_9, x_55, x_11, x_61);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_65, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_71 = x_65;
} else {
 lean_dec_ref(x_65);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_55);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_73 = lean_ctor_get(x_60, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_60, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_75 = x_60;
} else {
 lean_dec_ref(x_60);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_55);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_77 = lean_ctor_get(x_58, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_58, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_79 = x_58;
} else {
 lean_dec_ref(x_58);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_55);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_81 = lean_ctor_get(x_56, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_56, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_83 = x_56;
} else {
 lean_dec_ref(x_56);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabInductiveViews___lambda__2___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInductiveViews___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_13, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = lean_array_get_size(x_5);
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_20 = l_Array_toSubarray___rarg(x_5, x_19, x_18);
x_21 = lean_ctor_get(x_1, 6);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_17);
x_23 = lean_array_get_size(x_21);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(x_21, x_24, x_25, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_6);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_6, 7);
lean_dec(x_31);
lean_ctor_set(x_6, 7, x_29);
x_32 = l_Lean_Elab_Term_resetMessageLog(x_6, x_7, x_8, x_9, x_10, x_11, x_28);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_6);
x_34 = l_Lean_Elab_Term_addAutoBoundImplicits(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Command_elabInductiveViews___lambda__2___boxed__const__1;
x_38 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInductiveViews___lambda__1___boxed), 12, 5);
lean_closure_set(x_38, 0, x_2);
lean_closure_set(x_38, 1, x_35);
lean_closure_set(x_38, 2, x_3);
lean_closure_set(x_38, 3, x_4);
lean_closure_set(x_38, 4, x_37);
x_39 = l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(x_38, x_6, x_7, x_8, x_9, x_10, x_11, x_36);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_6);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_34, 0);
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_34);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_44 = lean_ctor_get(x_6, 0);
x_45 = lean_ctor_get(x_6, 1);
x_46 = lean_ctor_get(x_6, 2);
x_47 = lean_ctor_get(x_6, 3);
x_48 = lean_ctor_get(x_6, 4);
x_49 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
x_50 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 1);
x_51 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 2);
x_52 = lean_ctor_get(x_6, 5);
x_53 = lean_ctor_get(x_6, 6);
x_54 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 3);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_6);
x_55 = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(x_55, 0, x_44);
lean_ctor_set(x_55, 1, x_45);
lean_ctor_set(x_55, 2, x_46);
lean_ctor_set(x_55, 3, x_47);
lean_ctor_set(x_55, 4, x_48);
lean_ctor_set(x_55, 5, x_52);
lean_ctor_set(x_55, 6, x_53);
lean_ctor_set(x_55, 7, x_29);
lean_ctor_set_uint8(x_55, sizeof(void*)*8, x_49);
lean_ctor_set_uint8(x_55, sizeof(void*)*8 + 1, x_50);
lean_ctor_set_uint8(x_55, sizeof(void*)*8 + 2, x_51);
lean_ctor_set_uint8(x_55, sizeof(void*)*8 + 3, x_54);
x_56 = l_Lean_Elab_Term_resetMessageLog(x_55, x_7, x_8, x_9, x_10, x_11, x_28);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_55);
x_58 = l_Lean_Elab_Term_addAutoBoundImplicits(x_5, x_55, x_7, x_8, x_9, x_10, x_11, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Elab_Command_elabInductiveViews___lambda__2___boxed__const__1;
x_62 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInductiveViews___lambda__1___boxed), 12, 5);
lean_closure_set(x_62, 0, x_2);
lean_closure_set(x_62, 1, x_59);
lean_closure_set(x_62, 2, x_3);
lean_closure_set(x_62, 3, x_4);
lean_closure_set(x_62, 4, x_61);
x_63 = l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(x_62, x_55, x_7, x_8, x_9, x_10, x_11, x_60);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_55);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_58, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_66 = x_58;
} else {
 lean_dec_ref(x_58);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
uint8_t x_68; 
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
x_68 = !lean_is_exclusive(x_15);
if (x_68 == 0)
{
return x_15;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_15, 0);
x_70 = lean_ctor_get(x_15, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_15);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInductiveViews(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_5 = l_Lean_Elab_Command_instInhabitedInductiveView;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 3);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_9);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_Elab_Command_getScope___rarg(x_3, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 5);
lean_inc(x_14);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInductiveViews___lambda__2___boxed), 12, 4);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_8);
lean_closure_set(x_15, 2, x_1);
lean_closure_set(x_15, 3, x_9);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicit___rarg), 8, 1);
lean_closure_set(x_17, 0, x_16);
lean_inc(x_2);
x_18 = l_Lean_Elab_Command_liftTermElabM___rarg(x_10, x_17, x_2, x_3, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyDerivingHandlers(x_1, x_2, x_3, x_19);
lean_dec(x_1);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabInductiveViews___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabInductiveViews___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInductiveViews___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; lean_object* x_14; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Lean_Elab_Command_elabInductiveViews___lambda__1(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInductiveViews___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Command_elabInductiveViews___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_ReplaceLevel(lean_object*);
lean_object* initialize_Lean_Util_ReplaceExpr(lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(lean_object*);
lean_object* initialize_Lean_Meta_Constructions(lean_object*);
lean_object* initialize_Lean_Meta_CollectFVars(lean_object*);
lean_object* initialize_Lean_Meta_SizeOf(lean_object*);
lean_object* initialize_Lean_Meta_Injective(lean_object*);
lean_object* initialize_Lean_Meta_IndPredBelow(lean_object*);
lean_object* initialize_Lean_Elab_Command(lean_object*);
lean_object* initialize_Lean_Elab_DefView(lean_object*);
lean_object* initialize_Lean_Elab_DeclUtil(lean_object*);
lean_object* initialize_Lean_Elab_Deriving_Basic(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Inductive(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceLevel(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CollectFVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SizeOf(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Injective(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IndPredBelow(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DefView(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclUtil(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__1 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__1();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__1);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__2 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__2();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__2);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__3 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__3();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__3);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__4 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__4();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__4);
res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__1);
l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__2);
l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__3 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__3);
l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__4 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__1___closed__4);
l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__2___closed__1 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__2___closed__1);
l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__2___closed__2 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___rarg___lambda__2___closed__2);
l_Lean_Elab_Command_checkValidInductiveModifier___rarg___closed__1 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___rarg___closed__1);
l_Lean_Elab_Command_checkValidInductiveModifier___rarg___closed__2 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___rarg___closed__2);
l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__1___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__1___closed__2);
l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__2___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__2___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__2___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__2___closed__2);
l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__3___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__3___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__3___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___rarg___lambda__3___closed__2);
l_Lean_Elab_Command_checkValidCtorModifier___rarg___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___rarg___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___rarg___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___rarg___closed__2);
l_Lean_Elab_Command_instInhabitedCtorView___closed__1 = _init_l_Lean_Elab_Command_instInhabitedCtorView___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedCtorView___closed__1);
l_Lean_Elab_Command_instInhabitedCtorView___closed__2 = _init_l_Lean_Elab_Command_instInhabitedCtorView___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedCtorView___closed__2);
l_Lean_Elab_Command_instInhabitedCtorView___closed__3 = _init_l_Lean_Elab_Command_instInhabitedCtorView___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedCtorView___closed__3);
l_Lean_Elab_Command_instInhabitedCtorView = _init_l_Lean_Elab_Command_instInhabitedCtorView();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedCtorView);
l_Lean_Elab_Command_instInhabitedInductiveView___closed__1 = _init_l_Lean_Elab_Command_instInhabitedInductiveView___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedInductiveView___closed__1);
l_Lean_Elab_Command_instInhabitedInductiveView = _init_l_Lean_Elab_Command_instInhabitedInductiveView();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedInductiveView);
l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__1 = _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__1);
l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__2 = _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__2);
l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__3 = _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__3);
l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__4 = _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__4);
l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__5 = _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__5();
l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__6 = _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__6);
l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__7 = _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__7);
l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__8 = _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__8();
l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__9 = _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__9);
l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__10 = _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedElabHeaderResult___closed__10);
l_Lean_Elab_Command_instInhabitedElabHeaderResult = _init_l_Lean_Elab_Command_instInhabitedElabHeaderResult();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedElabHeaderResult);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__3 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__3);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__4 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__4);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__5 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__5);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__6 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__6);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__3 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__3);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___boxed__const__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___boxed__const__1);
l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__2 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__2);
l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__3 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__3);
l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__4 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___spec__1___closed__4);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2___closed__3 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___lambda__2___closed__3);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_checkParamOccs___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__2___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__2___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__2___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__2___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__3___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__3___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__3___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___lambda__3___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_elabCtorType___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___lambda__1___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___lambda__1___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___lambda__1___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___lambda__1___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__3 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__3);
l_Lean_Elab_Command_tmpIndParam___closed__1 = _init_l_Lean_Elab_Command_tmpIndParam___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_tmpIndParam___closed__1);
l_Lean_Elab_Command_tmpIndParam___closed__2 = _init_l_Lean_Elab_Command_tmpIndParam___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_tmpIndParam___closed__2);
l_Lean_Elab_Command_tmpIndParam___closed__3 = _init_l_Lean_Elab_Command_tmpIndParam___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_tmpIndParam___closed__3);
l_Lean_Elab_Command_tmpIndParam = _init_l_Lean_Elab_Command_tmpIndParam();
lean_mark_persistent(l_Lean_Elab_Command_tmpIndParam);
l_Lean_Elab_Command_shouldInferResultUniverse___closed__1 = _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_shouldInferResultUniverse___closed__1);
l_Lean_Elab_Command_shouldInferResultUniverse___closed__2 = _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_shouldInferResultUniverse___closed__2);
l_Lean_Elab_Command_shouldInferResultUniverse___closed__3 = _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_shouldInferResultUniverse___closed__3);
l_Lean_Elab_Command_shouldInferResultUniverse___closed__4 = _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_shouldInferResultUniverse___closed__4);
l_Lean_Elab_Command_accLevelAtCtor___closed__1 = _init_l_Lean_Elab_Command_accLevelAtCtor___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_accLevelAtCtor___closed__1);
l_Lean_Elab_Command_accLevelAtCtor___closed__2 = _init_l_Lean_Elab_Command_accLevelAtCtor___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_accLevelAtCtor___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__3 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__3);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__4 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__4);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__5 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__5);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__6 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__2___closed__6);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__1 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__1();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__1);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__2 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__2();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__2);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__3 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__3();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__3);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__4 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__4();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__4);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__5 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__5();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__5);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__6 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__6();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412____closed__6);
l_Lean_Elab_Command_bootstrap_inductiveCheckResultingUniverse___closed__1 = _init_l_Lean_Elab_Command_bootstrap_inductiveCheckResultingUniverse___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_bootstrap_inductiveCheckResultingUniverse___closed__1);
res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_3412_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Command_bootstrap_inductiveCheckResultingUniverse = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Command_bootstrap_inductiveCheckResultingUniverse);
lean_dec_ref(res);
l_Lean_Elab_Command_checkResultingUniverse___closed__1 = _init_l_Lean_Elab_Command_checkResultingUniverse___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkResultingUniverse___closed__1);
l_Lean_Elab_Command_checkResultingUniverse___closed__2 = _init_l_Lean_Elab_Command_checkResultingUniverse___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkResultingUniverse___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___closed__1);
l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__1 = _init_l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__1();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__1);
l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__2 = _init_l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__2();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__2);
l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__3 = _init_l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__3();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__3);
l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__4 = _init_l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__4();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__4);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___lambda__1___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__3 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__3);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__4 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__4);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__5 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__5);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__6 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__6);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__7 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__7);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__8 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__8);
l_Lean_Elab_Command_elabInductiveViews___lambda__2___boxed__const__1 = _init_l_Lean_Elab_Command_elabInductiveViews___lambda__2___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Command_elabInductiveViews___lambda__2___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
