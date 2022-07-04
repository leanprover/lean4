// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator.TopDownAnalyze
// Imports: Init Std.Data.RBMap Lean.Meta.SynthInstance Lean.Util.FindMVar Lean.Util.FindLevelMVar Lean.Util.CollectLevelParams Lean.Util.ReplaceLevel Lean.PrettyPrinter.Delaborator.Options Lean.PrettyPrinter.Delaborator.SubExpr Lean.Elab.Config
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
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__7;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingInfo_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getResetPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setBool(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeExplicitHoles___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isSimpleHOFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustSubtypeMk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__64;
uint8_t l_Lean_Expr_isNatLit(lean_object*);
lean_object* l_Lean_SubExpr_Pos_push(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_getPPInstances(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__2;
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_MetavarContext_findLevelDepth_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__5;
lean_object* l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__65;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__19;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__1;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__51;
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___boxed(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__2;
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__27;
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__67;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___closed__3;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__9;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__40;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisNamedArg___boxed(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__4;
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__4;
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___spec__1___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__39;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalyze___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__57;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustKnownFOType2TypeHOFuns(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___lambda__1(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__7;
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__5;
LEAN_EXPORT lean_object* l_Lean_pp_analyze_omitMax;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getPPAnalysisNamedArg___closed__1;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__11;
lean_object* l_Lean_SubExpr_Pos_toString(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__31;
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__6;
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__35;
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__5;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___closed__2;
static lean_object* l_Lean_getPPAnalysisNeedsType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_isCoe___closed__10;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzePi(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushNaryArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__4(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__58;
static lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__6;
static lean_object* l_Lean_getPPAnalysisBlockImplicit___closed__2;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__4;
static lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___closed__1;
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getPPAnalysisBlockImplicit___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisBlockImplicit___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__36;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__26;
static lean_object* l_Lean_getPPAnalysisNamedArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustSubtypeMk___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable(lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisSkip(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisNamedArg(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasParam(lean_object*);
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_isCoe(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_analyze_trustSubst;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__5___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__3;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isNonConstFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__3;
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaBoundedTelescope(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__2;
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__4;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__12;
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTypeAscriptions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__5;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_PrettyPrinter_Delaborator_topDownAnalyze___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__68;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__1;
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Meta_getPostponed___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SubExpr_Pos_root;
LEAN_EXPORT lean_object* l_Lean_pp_analyze_trustSubtypeMk;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_mvarName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__6;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeCheckInstances___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeKnowsType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_analyze_trustKnownFOType2TypeHOFuns;
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__10___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_Context_inBottomUp___default;
static lean_object* l_Lean_getPPAnalysisLetVarType___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__61;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isStructureInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__59;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_FindLevelMVar_main(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__3;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__2;
LEAN_EXPORT lean_object* l_Lean_pp_analyze_explicitHoles;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__1;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisLetVarType___boxed(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___boxed(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Std_RBNode_setBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__4;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__5;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisNeedsType___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_9562____closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustSubst(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__1;
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustId(lean_object*);
uint8_t l_Lean_getPPProofsWithType(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__2;
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_3187_(lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__1(lean_object*);
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_6____spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushNaryFn(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__6;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__20;
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__2;
static lean_object* l_Lean_getPPAnalysisNeedsType___closed__1;
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__2(uint8_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_800____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_341____spec__1(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1___closed__1;
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isDefEqAssigning(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_analyze_typeAscriptions;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder___closed__1;
static lean_object* l_Lean_getPPAnalysisSkip___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isFOLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Level_normalize___spec__1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__43;
uint8_t lean_is_out_param(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__7;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__1;
LEAN_EXPORT lean_object* l_Lean_pp_analyze;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__7;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__1;
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_Context_parentIsApp___default;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_analyze_checkInstances;
static uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__66;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__56;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps___spec__1___boxed(lean_object**);
static lean_object* l_Lean_getPPAnalysisSkip___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_setElabConfig(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_PrettyPrinter_Delaborator_topDownAnalyze___spec__1(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__3;
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__3;
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustId___boxed(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__4;
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__4;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__6;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__3(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__63;
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__2;
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__6;
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__1;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__24;
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__1;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__8;
static lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1___closed__3;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___closed__1;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___closed__2;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__8;
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__2;
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadWithReaderOfSubExprAnalyzeM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__4;
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__1;
size_t lean_usize_modn(size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346_(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__7;
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisHole(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeSort___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustCoe___boxed(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__32;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__10;
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__55;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_typeUnknown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_returnsPi___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkMaxHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustOfScientific(lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__53;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__42;
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeCheckInstances(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__2;
uint8_t l_Lean_getPPInstanceTypes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__1(lean_object*, size_t, size_t);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeOmitMax(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__2___boxed(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__2;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__49;
LEAN_EXPORT lean_object* l_Lean_pp_analyze_trustOfScientific;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext;
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike___closed__1;
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__16;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__4;
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustOfNat___boxed(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__4;
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_isCoe___closed__3;
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceOptions(lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeOmitMax___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustOfNat(lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyze(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isNonConstFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__4;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__3;
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__3;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__30;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__3;
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__2;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__14;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__9;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_returnsPi___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeSort___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__22;
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustCoe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__28;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__5;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_Lean_instInhabitedBinderInfo;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_isCoe___closed__2;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__5;
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_isCoe___closed__5;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__37;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_State_postponed___default;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_3187____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lambda__1(lean_object*);
static uint64_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__1;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___closed__2;
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
extern uint8_t l_instInhabitedBool;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_analyze_trustId;
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustSubst___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__3;
LEAN_EXPORT lean_object* l_Lean_pp_analyze_knowsType;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__29;
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__1;
static lean_object* l_Lean_PrettyPrinter_Delaborator_isCoe___closed__7;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable_containsNum___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeExplicitHoles(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_mvarName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable_containsNum(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t l_Std_RBNode_isRed___rarg(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__5;
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_getPPAnalysisHole___closed__1;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__18;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_isCoe___closed__8;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isStructureInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisHole___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_isCoe___closed__4;
static lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__1;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__52;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__4;
static lean_object* l_Lean_getPPAnalysisLetVarType___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_isCoe___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__2;
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_PrettyPrinter_Delaborator_returnsPi___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isCoe___boxed(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__3;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__15;
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__3;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__7;
static lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_9562____closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_getPPProofs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_isCoe___closed__9;
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__54;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__62;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__1;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustOfScientific___boxed(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisSkip___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadWithReaderOfSubExprAnalyzeM(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisBlockImplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeFailureId;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___boxed(lean_object**);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isFOLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__34;
static lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__3___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___lambda__1___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeSort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__23;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__2;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__2;
static lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__33;
static lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__5___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__13;
uint8_t l_Lean_Expr_isStringLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__2;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_returnsPi___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_362_(uint8_t, uint8_t);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__41;
uint8_t l_Lean_Expr_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__46;
uint8_t l_Lean_Expr_isAtomic(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__3;
LEAN_EXPORT lean_object* l_Lean_pp_analyze_trustCoe;
static lean_object* l_Lean_getPPAnalysisSkip___closed__4;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__25;
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustKnownFOType2TypeHOFuns___boxed(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__4;
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__4;
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__47;
static lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__6;
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___closed__2;
static lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__8;
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__1;
static lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisNeedsType(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__60;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_PrettyPrinter_Delaborator_returnsPi___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getPPAnalysisSkip___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__3;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_3187____closed__1;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__2;
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getPPAnalysisHole___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___spec__1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisLetVarType(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__6(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__48;
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeKnowsType(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__3___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__5;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___closed__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__4;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__50;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isType2Type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_9562_(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___spec__1___boxed(lean_object**);
static lean_object* l_Lean_PrettyPrinter_Delaborator_isCoe___closed__6;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__17;
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTypeAscriptions(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__44;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams___spec__1___boxed(lean_object**);
lean_object* l_Lean_Expr_isConstructorApp_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__21;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__38;
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__8;
static lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__3;
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isIdLike___boxed(lean_object*);
extern lean_object* l_Lean_SubExpr_Pos_typeCoord;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Meta_processPostponed(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_App_State_namedArgs___default;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_isIdLike(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedPUnit;
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__7___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_State_annotations___default;
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_returnsPi(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__10(lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_analyze_trustOfNat;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___lambda__1___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__3___boxed(lean_object**);
static lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__45;
static lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__1;
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pp", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("analyze", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__2;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pp.analyze", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(pretty printer analyzer) determine annotations sufficient to ensure round-tripping", 83);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__7() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__5;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__6;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__7;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_6____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("checkInstances", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(pretty printer analyzer) confirm that instances can be re-synthesized", 70);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__5;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__4;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_6____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("typeAscriptions", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(pretty printer analyzer) add type ascriptions when deemed necessary", 68);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__5;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__4;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_6____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("trustSubst", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(pretty printer analyzer) always 'pretend' applications that can delab to ▸ are 'regular'", 91);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__5;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__4;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_6____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("trustOfNat", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(pretty printer analyzer) always 'pretend' `OfNat.ofNat` applications can elab bottom-up", 88);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__5;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__4;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_6____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("trustOfScientific", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(pretty printer analyzer) always 'pretend' `OfScientific.ofScientific` applications can elab bottom-up", 102);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__5;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__4;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_6____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("trustCoe", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(pretty printer analyzer) always assume a coercion can be correctly inserted", 76);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__5;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__4;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_6____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("trustSubtypeMk", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(pretty printer analyzer) assume the implicit arguments of Subtype.mk can be inferred", 85);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__5;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__4;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_6____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("trustId", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(pretty printer analyzer) always assume an implicit `fun x => x` can be inferred", 80);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__5;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__4;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_6____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("trustKnownFOType2TypeHOFuns", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(pretty printer analyzer) omit higher-order functions whose values seem to be knownType2Type", 92);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__5;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__4;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_6____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("omitMax", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(pretty printer analyzer) omit universe `max` annotations (these constraints can actually hurt)", 95);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__5;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__4;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_6____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("knowsType", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(pretty printer analyzer) assume the type of the original expression is known", 77);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__5;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__4;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_6____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("explicitHoles", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(pretty printer analyzer) use `_` for explicit arguments that can be inferred", 77);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__5;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__4;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_6____spec__1(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyze(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyze___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyze(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeCheckInstances(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_checkInstances;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeCheckInstances___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeCheckInstances(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTypeAscriptions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_typeAscriptions;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTypeAscriptions___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeTypeAscriptions(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustSubst(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_trustSubst;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustSubst___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeTrustSubst(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustOfNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_trustOfNat;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustOfNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeTrustOfNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustOfScientific(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_trustOfScientific;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustOfScientific___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeTrustOfScientific(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_trustId;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustId___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeTrustId(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustCoe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_trustCoe;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustCoe___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeTrustCoe(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustSubtypeMk(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_trustSubtypeMk;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustSubtypeMk___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeTrustSubtypeMk(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeTrustKnownFOType2TypeHOFuns(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_trustKnownFOType2TypeHOFuns;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeTrustKnownFOType2TypeHOFuns___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeTrustKnownFOType2TypeHOFuns(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeOmitMax(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_omitMax;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeOmitMax___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeOmitMax(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeKnowsType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_knowsType;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeKnowsType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeKnowsType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalyzeExplicitHoles(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_pp_analyze_explicitHoles;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalyzeExplicitHoles___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalyzeExplicitHoles(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getPPAnalysisSkip___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("analysis", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_getPPAnalysisSkip___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__2;
x_2 = l_Lean_getPPAnalysisSkip___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getPPAnalysisSkip___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("skip", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_getPPAnalysisSkip___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getPPAnalysisSkip___closed__2;
x_2 = l_Lean_getPPAnalysisSkip___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisSkip(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalysisSkip___closed__4;
x_3 = l_Lean_KVMap_findCore(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisSkip___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalysisSkip(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getPPAnalysisHole___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hole", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_getPPAnalysisHole___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getPPAnalysisSkip___closed__2;
x_2 = l_Lean_getPPAnalysisHole___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisHole(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalysisHole___closed__2;
x_3 = l_Lean_KVMap_findCore(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisHole___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalysisHole(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getPPAnalysisNamedArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("namedArg", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_getPPAnalysisNamedArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getPPAnalysisSkip___closed__2;
x_2 = l_Lean_getPPAnalysisNamedArg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisNamedArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalysisNamedArg___closed__2;
x_3 = l_Lean_KVMap_findCore(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisNamedArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalysisNamedArg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getPPAnalysisLetVarType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("letVarType", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_getPPAnalysisLetVarType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getPPAnalysisSkip___closed__2;
x_2 = l_Lean_getPPAnalysisLetVarType___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisLetVarType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalysisLetVarType___closed__2;
x_3 = l_Lean_KVMap_findCore(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisLetVarType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalysisLetVarType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getPPAnalysisNeedsType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("needsType", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_getPPAnalysisNeedsType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getPPAnalysisSkip___closed__2;
x_2 = l_Lean_getPPAnalysisNeedsType___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisNeedsType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalysisNeedsType___closed__2;
x_3 = l_Lean_KVMap_findCore(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisNeedsType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalysisNeedsType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getPPAnalysisBlockImplicit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("blockImplicit", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_getPPAnalysisBlockImplicit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getPPAnalysisSkip___closed__2;
x_2 = l_Lean_getPPAnalysisBlockImplicit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_getPPAnalysisBlockImplicit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalysisBlockImplicit___closed__2;
x_3 = l_Lean_KVMap_findCore(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getPPAnalysisBlockImplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAnalysisBlockImplicit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_PrettyPrinter_Delaborator_returnsPi___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_PrettyPrinter_Delaborator_returnsPi___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_Lean_PrettyPrinter_Delaborator_returnsPi___spec__1___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_returnsPi___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Expr_isForall(x_2);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_returnsPi___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_returnsPi___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_returnsPi(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_PrettyPrinter_Delaborator_returnsPi___closed__1;
x_8 = l_Lean_Meta_lambdaTelescope___at_Lean_PrettyPrinter_Delaborator_returnsPi___spec__1___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_returnsPi___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_returnsPi___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isNonConstFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 2);
x_1 = x_7;
goto _start;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Expr_hasLooseBVars(x_1);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isNonConstFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_isNonConstFun(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isSimpleHOFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_PrettyPrinter_Delaborator_returnsPi___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_Meta_lambdaTelescope___at_Lean_PrettyPrinter_Delaborator_returnsPi___spec__1___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_PrettyPrinter_Delaborator_isNonConstFun(x_1, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_unbox(x_9);
lean_dec(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = 1;
x_18 = lean_box(x_17);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
lean_dec(x_24);
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set(x_11, 0, x_26);
return x_11;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_dec(x_11);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_11, 0);
lean_dec(x_32);
x_33 = 0;
x_34 = lean_box(x_33);
lean_ctor_set(x_11, 0, x_34);
return x_11;
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_dec(x_11);
x_36 = 0;
x_37 = lean_box(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_8);
if (x_39 == 0)
{
return x_8;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_8, 0);
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_8);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isType2Type(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 7)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 3)
{
lean_object* x_10; 
lean_dec(x_9);
x_10 = lean_ctor_get(x_8, 2);
lean_inc(x_10);
lean_dec(x_8);
if (lean_obj_tag(x_10) == 3)
{
uint8_t x_11; 
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_dec(x_12);
x_13 = 1;
x_14 = lean_box(x_13);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_10);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 0);
lean_dec(x_20);
x_21 = 0;
x_22 = lean_box(x_21);
lean_ctor_set(x_7, 0, x_22);
return x_7;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_dec(x_7);
x_24 = 0;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_7, 0);
lean_dec(x_28);
x_29 = 0;
x_30 = lean_box(x_29);
lean_ctor_set(x_7, 0, x_30);
return x_7;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_7, 1);
lean_inc(x_31);
lean_dec(x_7);
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_8);
x_35 = !lean_is_exclusive(x_7);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_7, 0);
lean_dec(x_36);
x_37 = 0;
x_38 = lean_box(x_37);
lean_ctor_set(x_7, 0, x_38);
return x_7;
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_dec(x_7);
x_40 = 0;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_7);
if (x_43 == 0)
{
return x_7;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_7, 0);
x_45 = lean_ctor_get(x_7, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_7);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isFOLike(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Expr_getAppFn(x_1);
x_8 = l_Lean_Expr_isFVar(x_7);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Expr_isConst(x_7);
lean_dec(x_7);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isFOLike___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_isFOLike(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_isIdLike(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isIdLike___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_isIdLike(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeT", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_isCoe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("coe", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_isCoe___closed__2;
x_2 = l_Lean_PrettyPrinter_Delaborator_isCoe___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeFun", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_isCoe___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_isCoe___closed__6;
x_2 = l_Lean_PrettyPrinter_Delaborator_isCoe___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CoeSort", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_isCoe___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_isCoe___closed__9;
x_2 = l_Lean_PrettyPrinter_Delaborator_isCoe___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_isCoe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_PrettyPrinter_Delaborator_isCoe___closed__4;
x_3 = lean_unsigned_to_nat(4u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_PrettyPrinter_Delaborator_isCoe___closed__7;
x_6 = l_Lean_Expr_isAppOf(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_PrettyPrinter_Delaborator_isCoe___closed__10;
x_8 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Expr_getAppNumArgsAux(x_1, x_9);
x_11 = lean_nat_dec_le(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_PrettyPrinter_Delaborator_isCoe___closed__10;
x_13 = l_Lean_Expr_isAppOfArity(x_1, x_12, x_3);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
}
else
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isCoe___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_isCoe(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isStructureInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_isConstructorApp_x3f(x_11, x_1);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
x_14 = lean_box(x_13);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_free_object(x_7);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_st_ref_get(x_5, x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = l_Lean_isStructure(x_19, x_20);
x_22 = lean_box(x_21);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = l_Lean_isStructure(x_25, x_26);
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_7, 0);
x_31 = lean_ctor_get(x_7, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_7);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Expr_isConstructorApp_x3f(x_32, x_1);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_st_ref_get(x_5, x_31);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_dec(x_37);
x_44 = l_Lean_isStructure(x_42, x_43);
x_45 = lean_box(x_44);
if (lean_is_scalar(x_41)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_41;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_isStructureInstance___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_isStructureInstance(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_Lean_MetavarContext_findDecl_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___lambda__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_box(0);
x_15 = l_Lean_FindMVar_main(x_13, x_1, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; lean_object* x_17; 
x_16 = 0;
x_17 = lean_box(x_16);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
else
{
uint8_t x_18; lean_object* x_19; 
lean_dec(x_15);
x_18 = 1;
x_19 = lean_box(x_18);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___lambda__1___boxed), 2, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_box(0);
x_25 = l_Lean_FindMVar_main(x_23, x_1, x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_25);
x_29 = 1;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_21);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___lambda__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
x_3 = l_Lean_MetavarContext_findLevelDepth_x3f(x_1, x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_800____at___private_Lean_Meta_Basic_0__Lean_Meta_beqInfoCacheKey____x40_Lean_Meta_Basic___hyg_341____spec__1(x_3, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___lambda__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_box(0);
x_15 = l_Lean_FindLevelMVar_main(x_13, x_1, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; lean_object* x_17; 
x_16 = 0;
x_17 = lean_box(x_16);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
else
{
uint8_t x_18; lean_object* x_19; 
lean_dec(x_15);
x_18 = 1;
x_19 = lean_box(x_18);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___lambda__1___boxed), 2, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_box(0);
x_25 = l_Lean_FindLevelMVar_main(x_23, x_1, x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_25);
x_29 = 1;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_21);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___lambda__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasMVarAtCurrDepth(x_8, x_2, x_3, x_4, x_5, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_typeUnknown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(x_8, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Expr_constName_x21(x_1);
x_8 = lean_name_eq(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
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
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HOr", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hOr", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__2;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HXor", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hXor", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__6;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HAnd", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hAnd", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__10;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HAppend", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hAppend", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__14;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HOrElse", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hOrElse", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__18;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HAndThen", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__21;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hAndThen", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__22;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__23;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HAdd", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__25;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hAdd", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__26;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__27;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HSub", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__29;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hSub", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__30;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__31;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HMul", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__33;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hMul", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__34;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__35;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HDiv", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__37;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hDiv", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__38;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__39;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__41() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HMod", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__41;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__43() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hMod", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__42;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__43;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HShiftLeft", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__45;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__47() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hShiftLeft", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__46;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__47;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__49() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HShiftRight", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__49;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(13u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__51;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__52;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__53;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__12;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__54;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__16;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__55;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__20;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__56;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__24;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__57;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__28;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__58;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__32;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__59;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__36;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__60;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__40;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__61;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__44;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__62;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__48;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__64() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__63;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__50;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__64;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__66() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__65;
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
static uint8_t _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__67() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__65;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__68() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__65;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_dec(x_2);
x_3 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__66;
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__67;
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
size_t x_7; lean_object* x_8; size_t x_9; uint8_t x_10; 
x_7 = 0;
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__64;
x_9 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__68;
x_10 = l_Array_anyMUnsafe_any___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___spec__1(x_1, x_8, x_7, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
lean_dec(x_2);
x_3 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
x_4 = l_Lean_Expr_isConst(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1(x_3, x_6);
lean_dec(x_3);
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Expr_getAppNumArgsAux(x_1, x_2);
x_4 = lean_unsigned_to_nat(6u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__2(x_1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__2(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = lean_uint64_to_usize(x_7);
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l_Lean_Name_hash(x_13);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_modn(x_18, x_16);
lean_dec(x_16);
x_20 = lean_array_uget(x_1, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_uset(x_1, x_19, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_AssocList_foldlM___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__6(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_AssocList_replace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__7(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_name_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_AssocList_replace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__7(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_uint64_to_usize(x_8);
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Std_AssocList_contains___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__3(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
x_16 = lean_array_uset(x_6, x_10, x_15);
x_17 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_14);
x_18 = lean_nat_dec_le(x_17, x_7);
lean_dec(x_7);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_Std_HashMapImp_expand___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__4(x_14, x_16);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_Std_AssocList_replace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__7(x_2, x_3, x_11);
x_21 = lean_array_uset(x_6, x_10, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = l_Lean_Name_hash(x_2);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_modn(x_26, x_24);
x_28 = lean_array_uget(x_23, x_27);
x_29 = l_Std_AssocList_contains___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__3(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_22, x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_23, x_27, x_32);
x_34 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_31);
x_35 = lean_nat_dec_le(x_34, x_24);
lean_dec(x_24);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_HashMapImp_expand___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__4(x_31, x_33);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_Std_AssocList_replace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__7(x_2, x_3, x_28);
x_39 = lean_array_uset(x_23, x_27, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_12 = lean_array_uget(x_1, x_3);
x_13 = l_Lean_Meta_mkFreshLevelMVar(x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Std_HashMap_insert___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__2(x_4, x_12, x_14);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_4 = x_16;
x_9 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__10(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Std.Data.HashMap", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Std.HashMap.find!", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("key is not in the map", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__1;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__2;
x_3 = lean_unsigned_to_nat(177u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Std_HashMapImp_find_x3f___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__9(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__4;
x_6 = l_panic___at_Lean_Level_normalize___spec__1(x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
else
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = l_Lean_Level_hasParam(x_2);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_2);
x_13 = lean_box(0);
return x_13;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__1;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__2;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; uint8_t x_17; 
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__3;
lean_inc(x_1);
x_9 = l_Lean_CollectLevelParams_main(x_1, x_8);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Std_mkHashMapImp___rarg(x_11);
x_13 = lean_array_get_size(x_10);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = l_Array_forInUnsafe_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__8(x_10, x_14, x_15, x_12, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1), 2, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_19, x_1);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1), 2, 1);
lean_closure_set(x_23, 0, x_21);
x_24 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(x_23, x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Expr_hasLevelParam(x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2(x_1, x_9, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__8(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___spec__10(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isDefEqAssigning(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
lean_ctor_set_uint8(x_9, 10, x_11);
x_12 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_13 = lean_ctor_get_uint8(x_9, 0);
x_14 = lean_ctor_get_uint8(x_9, 1);
x_15 = lean_ctor_get_uint8(x_9, 2);
x_16 = lean_ctor_get_uint8(x_9, 3);
x_17 = lean_ctor_get_uint8(x_9, 4);
x_18 = lean_ctor_get_uint8(x_9, 5);
x_19 = lean_ctor_get_uint8(x_9, 6);
x_20 = lean_ctor_get_uint8(x_9, 7);
x_21 = lean_ctor_get_uint8(x_9, 8);
x_22 = lean_ctor_get_uint8(x_9, 9);
x_23 = lean_ctor_get_uint8(x_9, 11);
x_24 = lean_ctor_get_uint8(x_9, 12);
x_25 = lean_ctor_get_uint8(x_9, 13);
lean_dec(x_9);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_27, 0, x_13);
lean_ctor_set_uint8(x_27, 1, x_14);
lean_ctor_set_uint8(x_27, 2, x_15);
lean_ctor_set_uint8(x_27, 3, x_16);
lean_ctor_set_uint8(x_27, 4, x_17);
lean_ctor_set_uint8(x_27, 5, x_18);
lean_ctor_set_uint8(x_27, 6, x_19);
lean_ctor_set_uint8(x_27, 7, x_20);
lean_ctor_set_uint8(x_27, 8, x_21);
lean_ctor_set_uint8(x_27, 9, x_22);
lean_ctor_set_uint8(x_27, 10, x_26);
lean_ctor_set_uint8(x_27, 11, x_23);
lean_ctor_set_uint8(x_27, 12, x_24);
lean_ctor_set_uint8(x_27, 13, x_25);
lean_ctor_set(x_3, 0, x_27);
x_28 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_ctor_get(x_3, 1);
x_31 = lean_ctor_get(x_3, 2);
x_32 = lean_ctor_get(x_3, 3);
x_33 = lean_ctor_get(x_3, 4);
x_34 = lean_ctor_get(x_3, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_3);
x_35 = lean_ctor_get_uint8(x_29, 0);
x_36 = lean_ctor_get_uint8(x_29, 1);
x_37 = lean_ctor_get_uint8(x_29, 2);
x_38 = lean_ctor_get_uint8(x_29, 3);
x_39 = lean_ctor_get_uint8(x_29, 4);
x_40 = lean_ctor_get_uint8(x_29, 5);
x_41 = lean_ctor_get_uint8(x_29, 6);
x_42 = lean_ctor_get_uint8(x_29, 7);
x_43 = lean_ctor_get_uint8(x_29, 8);
x_44 = lean_ctor_get_uint8(x_29, 9);
x_45 = lean_ctor_get_uint8(x_29, 11);
x_46 = lean_ctor_get_uint8(x_29, 12);
x_47 = lean_ctor_get_uint8(x_29, 13);
if (lean_is_exclusive(x_29)) {
 x_48 = x_29;
} else {
 lean_dec_ref(x_29);
 x_48 = lean_box(0);
}
x_49 = 1;
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 0, 14);
} else {
 x_50 = x_48;
}
lean_ctor_set_uint8(x_50, 0, x_35);
lean_ctor_set_uint8(x_50, 1, x_36);
lean_ctor_set_uint8(x_50, 2, x_37);
lean_ctor_set_uint8(x_50, 3, x_38);
lean_ctor_set_uint8(x_50, 4, x_39);
lean_ctor_set_uint8(x_50, 5, x_40);
lean_ctor_set_uint8(x_50, 6, x_41);
lean_ctor_set_uint8(x_50, 7, x_42);
lean_ctor_set_uint8(x_50, 8, x_43);
lean_ctor_set_uint8(x_50, 9, x_44);
lean_ctor_set_uint8(x_50, 10, x_49);
lean_ctor_set_uint8(x_50, 11, x_45);
lean_ctor_set_uint8(x_50, 12, x_46);
lean_ctor_set_uint8(x_50, 13, x_47);
x_51 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_30);
lean_ctor_set(x_51, 2, x_31);
lean_ctor_set(x_51, 3, x_32);
lean_ctor_set(x_51, 4, x_33);
lean_ctor_set(x_51, 5, x_34);
x_52 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_51, x_4, x_5, x_6, x_7);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; 
x_9 = l_Lean_Meta_saveState___rarg(x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isDefEqAssigning(x_1, x_2, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_13);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = 0;
x_31 = lean_box(x_30);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_dec(x_23);
x_37 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Lean_Meta_processPostponed(x_3, x_37, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_13);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(x_37);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(x_37);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_10);
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
lean_dec(x_38);
x_50 = l_Lean_Meta_getPostponed___rarg(x_5, x_6, x_7, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Std_PersistentArray_append___rarg(x_13, x_51);
x_54 = l_Lean_Meta_setPostponed(x_53, x_4, x_5, x_6, x_7, x_52);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = 1;
x_58 = lean_box(x_57);
lean_ctor_set(x_54, 0, x_58);
return x_54;
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = 1;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_13);
x_63 = lean_ctor_get(x_38, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_38, 1);
lean_inc(x_64);
lean_dec(x_38);
x_15 = x_63;
x_16 = x_64;
goto block_22;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_13);
x_65 = lean_ctor_get(x_23, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_23, 1);
lean_inc(x_66);
lean_dec(x_23);
x_15 = x_65;
x_16 = x_66;
goto block_22;
}
block_22:
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Meta_SavedState_restore(x_10, x_4, x_5, x_6, x_7, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l_Lean_Meta_checkpointDefEq___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq___spec__1(x_1, x_2, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkpointDefEq___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_checkpointDefEq___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq___spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
lean_dec(x_8);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Expr_isSort(x_2);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder___closed__1;
x_8 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
lean_dec(x_8);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike___closed__1;
x_11 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_8, x_10, x_2, x_3, x_4, x_5, x_9);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Eq", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ndrec", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__2;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rec", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__2;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__4;
x_3 = lean_unsigned_to_nat(6u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__6;
x_6 = l_Lean_Expr_isAppOfArity(x_1, x_5, x_3);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable_containsNum(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
x_1 = x_3;
goto _start;
}
default: 
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable_containsNum___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable_containsNum(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Name_hasMacroScopes(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_isPrivateName(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable_containsNum(x_1);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_mvarName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Expr_mvarId_x21(x_1);
x_8 = l_Lean_Meta_getMVarDecl(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
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
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_mvarName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_mvarName(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
x_1 = x_2;
goto _start;
}
case 2:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Level_hasParam(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax(x_4);
if (x_7 == 0)
{
x_1 = x_5;
goto _start;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = l_Lean_Level_hasParam(x_5);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax(x_4);
if (x_11 == 0)
{
x_1 = x_5;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
}
case 3:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = l_Lean_Level_hasParam(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax(x_15);
if (x_18 == 0)
{
x_1 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = l_Lean_Level_hasParam(x_16);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax(x_15);
if (x_22 == 0)
{
x_1 = x_16;
goto _start;
}
else
{
uint8_t x_24; 
x_24 = 1;
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = 1;
return x_25;
}
}
}
default: 
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static uint8_t _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_Context_inBottomUp___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint8_t _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_Context_parentIsApp___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static uint64_t _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__1;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__2;
x_2 = l_Lean_SubExpr_Pos_root;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__3;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 1, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 2, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_State_annotations___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_State_postponed___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_apply_1(x_1, x_12);
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
x_16 = lean_apply_1(x_1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___spec__2___rarg), 9, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___spec__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___closed__1;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___spec__2___rarg), 9, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_ReaderT_read___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadWithReaderOfSubExprAnalyzeM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_apply_1(x_1, x_11);
lean_ctor_set(x_3, 0, x_12);
x_13 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_15 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 3);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_apply_1(x_1, x_18);
x_20 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_14);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 1, x_15);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 2, x_16);
lean_ctor_set_uint8(x_20, sizeof(void*)*1 + 3, x_17);
x_21 = lean_apply_7(x_2, x_20, x_4, x_5, x_6, x_7, x_8, x_9);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadWithReaderOfSubExprAnalyzeM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadWithReaderOfSubExprAnalyzeM___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_38; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_38 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isDefEqAssigning(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___closed__1;
x_42 = lean_unbox(x_39);
lean_dec(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_st_ref_get(x_8, x_40);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_st_ref_take(x_4, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_2);
lean_inc(x_1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_2);
x_51 = lean_array_push(x_49, x_50);
lean_ctor_set(x_46, 1, x_51);
x_52 = lean_st_ref_set(x_4, x_46, x_47);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_box(0);
lean_inc(x_8);
lean_inc(x_4);
x_55 = lean_apply_8(x_41, x_54, x_3, x_4, x_5, x_6, x_7, x_8, x_53);
if (lean_obj_tag(x_55) == 0)
{
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_55;
}
else
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_10 = x_56;
goto block_37;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_57 = lean_ctor_get(x_46, 0);
x_58 = lean_ctor_get(x_46, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_46);
lean_inc(x_2);
lean_inc(x_1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_2);
x_60 = lean_array_push(x_58, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_st_ref_set(x_4, x_61, x_47);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_box(0);
lean_inc(x_8);
lean_inc(x_4);
x_65 = lean_apply_8(x_41, x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_10 = x_66;
goto block_37;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_box(0);
lean_inc(x_8);
lean_inc(x_4);
x_68 = lean_apply_8(x_41, x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
if (lean_obj_tag(x_68) == 0)
{
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_68;
}
else
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_10 = x_69;
goto block_37;
}
}
}
else
{
lean_object* x_70; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_70 = lean_ctor_get(x_38, 1);
lean_inc(x_70);
lean_dec(x_38);
x_10 = x_70;
goto block_37;
}
block_37:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_8, x_10);
lean_dec(x_8);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
x_19 = lean_array_push(x_17, x_18);
lean_ctor_set(x_14, 1, x_19);
x_20 = lean_st_ref_set(x_4, x_14, x_15);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_2);
x_30 = lean_array_push(x_28, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_st_ref_set(x_4, x_31, x_15);
lean_dec(x_4);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
x_14 = l_Lean_instInhabitedExpr;
x_15 = lean_array_get(x_14, x_1, x_2);
x_16 = lean_expr_instantiate1(x_3, x_15);
lean_dec(x_15);
lean_dec(x_3);
x_17 = lean_array_get(x_14, x_4, x_2);
x_18 = lean_expr_instantiate1(x_5, x_17);
lean_dec(x_17);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_21 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux(x_16, x_18, x_20, x_1, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_dec(x_6);
if (lean_obj_tag(x_1) == 7)
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_is_out_param(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux___lambda__1(x_3, x_4, x_15, x_5, x_16, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l_Lean_instInhabitedExpr;
x_21 = lean_array_get(x_20, x_3, x_4);
x_22 = lean_array_get(x_20, x_5, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_23 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_21, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux___lambda__1(x_3, x_4, x_15, x_5, x_16, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_13);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_13);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_13 = lean_whnf(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_16 = lean_whnf(x_2, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_array_get_size(x_4);
x_21 = lean_nat_dec_lt(x_3, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
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
x_22 = lean_box(0);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_16);
x_23 = lean_box(0);
x_24 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux___lambda__2(x_14, x_18, x_4, x_3, x_5, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_array_get_size(x_4);
x_28 = lean_nat_dec_lt(x_3, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
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
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux___lambda__2(x_14, x_25, x_4, x_3, x_5, x_31, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
return x_32;
}
}
}
else
{
uint8_t x_33; 
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
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
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
x_37 = !lean_is_exclusive(x_13);
if (x_37 == 0)
{
return x_13;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_13, 0);
x_39 = lean_ctor_get(x_13, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_13);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_infer_type(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = lean_infer_type(x_2, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Expr_getAppFn(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = lean_infer_type(x_16, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_getAppFn(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = lean_infer_type(x_20, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Expr_getAppNumArgsAux(x_11, x_24);
x_26 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams___closed__1;
lean_inc(x_25);
x_27 = lean_mk_array(x_25, x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_25, x_28);
lean_dec(x_25);
x_30 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_11, x_27, x_29);
x_31 = l_Lean_Expr_getAppNumArgsAux(x_14, x_24);
lean_inc(x_31);
x_32 = lean_mk_array(x_31, x_26);
x_33 = lean_nat_sub(x_31, x_28);
lean_dec(x_31);
x_34 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_14, x_32, x_33);
x_35 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams_inspectAux(x_18, x_22, x_24, x_30, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
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
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_17);
if (x_40 == 0)
{
return x_17;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_17, 0);
x_42 = lean_ctor_get(x_17, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_17);
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
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_13);
if (x_44 == 0)
{
return x_13;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_13, 0);
x_46 = lean_ctor_get(x_13, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_13);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_10);
if (x_48 == 0)
{
return x_10;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_10, 0);
x_50 = lean_ctor_get(x_10, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_10);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("OfScientific", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ofScientific", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__2;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("OfNat", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ofNat", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__6;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 2);
x_10 = l_Lean_Expr_isFVar(x_1);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isConst(x_1);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isMVar(x_1);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isNatLit(x_1);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isStringLit(x_1);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Expr_isSort(x_1);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_getPPAnalyzeTrustOfNat(x_9);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_getPPAnalyzeTrustOfScientific(x_9);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__4;
x_22 = lean_unsigned_to_nat(5u);
x_23 = l_Lean_Expr_isAppOfArity(x_1, x_21, x_22);
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__8;
x_27 = lean_unsigned_to_nat(3u);
x_28 = l_Lean_Expr_isAppOfArity(x_1, x_26, x_27);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_getPPAnalyzeTrustOfScientific(x_9);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_8);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_33 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__4;
x_34 = lean_unsigned_to_nat(5u);
x_35 = l_Lean_Expr_isAppOfArity(x_1, x_33, x_34);
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_8);
return x_37;
}
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_38 = 1;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_8);
return x_40;
}
}
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_41 = 1;
x_42 = lean_box(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_8);
return x_43;
}
}
else
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_44 = 1;
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_8);
return x_46;
}
}
else
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_47 = 1;
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_8);
return x_49;
}
}
else
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_50 = 1;
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_8);
return x_52;
}
}
else
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_53 = 1;
x_54 = lean_box(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_8);
return x_55;
}
}
else
{
uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_56 = 1;
x_57 = lean_box(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_8);
return x_58;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_7, x_6);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_5, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; 
lean_dec(x_9);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_5, x_20);
lean_dec(x_5);
x_28 = l_Lean_instInhabitedBinderInfo;
x_29 = lean_box(x_28);
x_30 = lean_array_get(x_29, x_4, x_6);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
x_32 = 3;
x_33 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_362_(x_31, x_32);
if (x_33 == 0)
{
uint8_t x_34; uint8_t x_35; 
x_34 = 0;
x_35 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_362_(x_31, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_22 = x_36;
x_23 = x_16;
goto block_27;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = l_Lean_instInhabitedExpr;
x_38 = lean_array_get(x_37, x_2, x_6);
x_39 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp(x_38, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_array_get(x_37, x_3, x_6);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_43);
x_44 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_typeUnknown(x_43, x_12, x_13, x_14, x_15, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_43);
lean_dec(x_38);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_22 = x_48;
x_23 = x_47;
goto block_27;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_dec(x_44);
lean_inc(x_43);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_43);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_38);
x_51 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp(x_38, x_50, x_1, x_10, x_11, x_12, x_13, x_14, x_15, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_43);
lean_dec(x_38);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_22 = x_55;
x_23 = x_54;
goto block_27;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_dec(x_51);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_57 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_38, x_43, x_10, x_11, x_12, x_13, x_14, x_15, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_22 = x_59;
x_23 = x_58;
goto block_27;
}
else
{
uint8_t x_60; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_57, 0);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_57);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_43);
lean_dec(x_38);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_51);
if (x_64 == 0)
{
return x_51;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_51, 0);
x_66 = lean_ctor_get(x_51, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_51);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_43);
lean_dec(x_38);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_44);
if (x_68 == 0)
{
return x_44;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_44, 0);
x_70 = lean_ctor_get(x_44, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_44);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_39, 1);
lean_inc(x_72);
lean_dec(x_39);
x_73 = lean_array_get(x_37, x_3, x_6);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_74 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_38, x_73, x_10, x_11, x_12, x_13, x_14, x_15, x_72);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_22 = x_76;
x_23 = x_75;
goto block_27;
}
else
{
uint8_t x_77; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_74);
if (x_77 == 0)
{
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_74, 0);
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_74);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = l_Lean_instInhabitedExpr;
x_82 = lean_array_get(x_81, x_2, x_6);
x_83 = lean_array_get(x_81, x_3, x_6);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_84 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams(x_82, x_83, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_22 = x_86;
x_23 = x_85;
goto block_27;
}
else
{
uint8_t x_87; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_84);
if (x_87 == 0)
{
return x_84;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_84, 0);
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_84);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
block_27:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_21;
x_6 = x_25;
x_9 = x_24;
x_16 = x_23;
goto _start;
}
}
else
{
lean_object* x_91; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_9);
lean_ctor_set(x_91, 1, x_16);
return x_91;
}
}
else
{
lean_object* x_92; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_9);
lean_ctor_set(x_92, 1, x_16);
return x_92;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(x_1, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = 1;
x_16 = lean_box(x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
lean_dec(x_22);
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_10, 0, x_24);
return x_10;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_dec(x_10);
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___lambda__1(x_1, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = lean_infer_type(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_17 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_1, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___lambda__1(x_1, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_18);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Expr_getAppNumArgsAux(x_1, x_13);
x_15 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams___closed__1;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
lean_inc(x_1);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_16, x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_20 = lean_infer_type(x_2, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_23 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars(x_21, x_8, x_9, x_10, x_11, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_array_get_size(x_19);
x_27 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_28 = l_Lean_Meta_forallMetaBoundedTelescope(x_24, x_26, x_27, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_array_get_size(x_32);
x_36 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_35);
x_37 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1(x_3, x_19, x_32, x_33, x_35, x_13, x_35, x_17, x_36, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_19);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp(x_1);
if (x_39 == 0)
{
x_40 = x_39;
x_41 = x_38;
goto block_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = l_Lean_instInhabitedExpr;
x_56 = lean_array_get(x_55, x_32, x_13);
x_57 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(x_56, x_8, x_9, x_10, x_11, x_38);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_58);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_array_get(x_55, x_32, x_17);
x_62 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(x_61, x_8, x_9, x_10, x_11, x_60);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_unbox(x_63);
lean_dec(x_63);
x_40 = x_65;
x_41 = x_64;
goto block_54;
}
else
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
lean_dec(x_57);
x_67 = lean_unbox(x_58);
lean_dec(x_58);
x_40 = x_67;
x_41 = x_66;
goto block_54;
}
}
block_54:
{
if (x_40 == 0)
{
lean_object* x_42; 
lean_dec(x_32);
x_42 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___lambda__2(x_34, x_4, x_36, x_6, x_7, x_8, x_9, x_10, x_11, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = l_Lean_instInhabitedExpr;
x_44 = lean_array_get(x_43, x_32, x_13);
x_45 = lean_array_get(x_43, x_32, x_17);
lean_dec(x_32);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_44, x_45, x_6, x_7, x_8, x_9, x_10, x_11, x_41);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___lambda__2(x_34, x_4, x_47, x_6, x_7, x_8, x_9, x_10, x_11, x_48);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_34);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 0);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_46);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_37);
if (x_68 == 0)
{
return x_37;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_37, 0);
x_70 = lean_ctor_get(x_37, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_37);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_28);
if (x_72 == 0)
{
return x_28;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_28, 0);
x_74 = lean_ctor_get(x_28, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_28);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_20);
if (x_76 == 0)
{
return x_20;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_20, 0);
x_78 = lean_ctor_get(x_20, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_20);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_4);
x_12 = l_Lean_Expr_getAppFn(x_1);
x_13 = l_Lean_Expr_isConst(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isFVar(x_12);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___lambda__3(x_1, x_12, x_2, x_3, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___lambda__3(x_1, x_12, x_2, x_3, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_3, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
lean_dec(x_3);
x_15 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___lambda__4(x_1, x_14, x_2, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
lean_dec(x_22);
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_dec(x_15);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_10);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; 
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 1, x_2);
x_12 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
else
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 2);
x_14 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 3);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_1);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 1, x_2);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 2, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 3, x_14);
x_17 = lean_apply_7(x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_3187____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("analyzeFailure", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_3187____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_3187____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_3187_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_3187____closed__2;
x_3 = l_Lean_registerInternalExceptionId(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeFailureId;
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___closed__2;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_nat_dec_lt(x_2, x_10);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = lean_nat_dec_eq(x_2, x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__2(x_12, x_2, x_3);
x_16 = 0;
lean_ctor_set(x_1, 3, x_15);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_10);
x_17 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_17);
return x_1;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__2(x_9, x_2, x_3);
x_19 = 0;
lean_ctor_set(x_1, 0, x_18);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = lean_nat_dec_lt(x_2, x_21);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_nat_dec_eq(x_2, x_21);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__2(x_23, x_2, x_3);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; 
lean_dec(x_22);
lean_dec(x_21);
x_29 = 0;
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_3);
lean_ctor_set(x_30, 3, x_23);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_29);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__2(x_20, x_2, x_3);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = lean_nat_dec_lt(x_2, x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = lean_nat_dec_eq(x_2, x_36);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Std_RBNode_isRed___rarg(x_38);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__2(x_38, x_2, x_3);
x_43 = 1;
lean_ctor_set(x_1, 3, x_42);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__2(x_38, x_2, x_3);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 3);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_44, 3);
lean_dec(x_48);
x_49 = lean_ctor_get(x_44, 0);
lean_dec(x_49);
x_50 = 0;
lean_ctor_set(x_44, 0, x_46);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_50);
x_51 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_51);
return x_1;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_44, 1);
x_53 = lean_ctor_get(x_44, 2);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_44);
x_54 = 0;
x_55 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_53);
lean_ctor_set(x_55, 3, x_46);
lean_ctor_set_uint8(x_55, sizeof(void*)*4, x_54);
x_56 = 1;
lean_ctor_set(x_1, 3, x_55);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_56);
return x_1;
}
}
else
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_46, sizeof(void*)*4);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_44);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_44, 1);
x_60 = lean_ctor_get(x_44, 2);
x_61 = lean_ctor_get(x_44, 3);
lean_dec(x_61);
x_62 = lean_ctor_get(x_44, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_46);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; 
x_64 = lean_ctor_get(x_46, 0);
x_65 = lean_ctor_get(x_46, 1);
x_66 = lean_ctor_get(x_46, 2);
x_67 = lean_ctor_get(x_46, 3);
x_68 = 1;
lean_ctor_set(x_46, 3, x_45);
lean_ctor_set(x_46, 2, x_37);
lean_ctor_set(x_46, 1, x_36);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_68);
lean_ctor_set(x_44, 3, x_67);
lean_ctor_set(x_44, 2, x_66);
lean_ctor_set(x_44, 1, x_65);
lean_ctor_set(x_44, 0, x_64);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_68);
x_69 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_60);
lean_ctor_set(x_1, 1, x_59);
lean_ctor_set(x_1, 0, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; uint8_t x_76; 
x_70 = lean_ctor_get(x_46, 0);
x_71 = lean_ctor_get(x_46, 1);
x_72 = lean_ctor_get(x_46, 2);
x_73 = lean_ctor_get(x_46, 3);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_46);
x_74 = 1;
x_75 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_75, 0, x_35);
lean_ctor_set(x_75, 1, x_36);
lean_ctor_set(x_75, 2, x_37);
lean_ctor_set(x_75, 3, x_45);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_74);
lean_ctor_set(x_44, 3, x_73);
lean_ctor_set(x_44, 2, x_72);
lean_ctor_set(x_44, 1, x_71);
lean_ctor_set(x_44, 0, x_70);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_74);
x_76 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_60);
lean_ctor_set(x_1, 1, x_59);
lean_ctor_set(x_1, 0, x_75);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_76);
return x_1;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_77 = lean_ctor_get(x_44, 1);
x_78 = lean_ctor_get(x_44, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_44);
x_79 = lean_ctor_get(x_46, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_46, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_46, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_46, 3);
lean_inc(x_82);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_83 = x_46;
} else {
 lean_dec_ref(x_46);
 x_83 = lean_box(0);
}
x_84 = 1;
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(1, 4, 1);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_35);
lean_ctor_set(x_85, 1, x_36);
lean_ctor_set(x_85, 2, x_37);
lean_ctor_set(x_85, 3, x_45);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_84);
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_80);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_82);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_84);
x_87 = 0;
lean_ctor_set(x_1, 3, x_86);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_85);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_87);
return x_1;
}
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_44);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_44, 3);
lean_dec(x_89);
x_90 = lean_ctor_get(x_44, 0);
lean_dec(x_90);
x_91 = 0;
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_91);
x_92 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_44, 1);
x_94 = lean_ctor_get(x_44, 2);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_44);
x_95 = 0;
x_96 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_96, 0, x_45);
lean_ctor_set(x_96, 1, x_93);
lean_ctor_set(x_96, 2, x_94);
lean_ctor_set(x_96, 3, x_46);
lean_ctor_set_uint8(x_96, sizeof(void*)*4, x_95);
x_97 = 1;
lean_ctor_set(x_1, 3, x_96);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_97);
return x_1;
}
}
}
}
else
{
uint8_t x_98; 
x_98 = lean_ctor_get_uint8(x_45, sizeof(void*)*4);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_44);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_44, 0);
lean_dec(x_100);
x_101 = !lean_is_exclusive(x_45);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_107; 
x_102 = lean_ctor_get(x_45, 0);
x_103 = lean_ctor_get(x_45, 1);
x_104 = lean_ctor_get(x_45, 2);
x_105 = lean_ctor_get(x_45, 3);
x_106 = 1;
lean_ctor_set(x_45, 3, x_102);
lean_ctor_set(x_45, 2, x_37);
lean_ctor_set(x_45, 1, x_36);
lean_ctor_set(x_45, 0, x_35);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_106);
lean_ctor_set(x_44, 0, x_105);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_106);
x_107 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_104);
lean_ctor_set(x_1, 1, x_103);
lean_ctor_set(x_1, 0, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_107);
return x_1;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; uint8_t x_114; 
x_108 = lean_ctor_get(x_45, 0);
x_109 = lean_ctor_get(x_45, 1);
x_110 = lean_ctor_get(x_45, 2);
x_111 = lean_ctor_get(x_45, 3);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_45);
x_112 = 1;
x_113 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_113, 0, x_35);
lean_ctor_set(x_113, 1, x_36);
lean_ctor_set(x_113, 2, x_37);
lean_ctor_set(x_113, 3, x_108);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_112);
lean_ctor_set(x_44, 0, x_111);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_112);
x_114 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_110);
lean_ctor_set(x_1, 1, x_109);
lean_ctor_set(x_1, 0, x_113);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_114);
return x_1;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_115 = lean_ctor_get(x_44, 1);
x_116 = lean_ctor_get(x_44, 2);
x_117 = lean_ctor_get(x_44, 3);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_44);
x_118 = lean_ctor_get(x_45, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_45, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_45, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_45, 3);
lean_inc(x_121);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_122 = x_45;
} else {
 lean_dec_ref(x_45);
 x_122 = lean_box(0);
}
x_123 = 1;
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(1, 4, 1);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_35);
lean_ctor_set(x_124, 1, x_36);
lean_ctor_set(x_124, 2, x_37);
lean_ctor_set(x_124, 3, x_118);
lean_ctor_set_uint8(x_124, sizeof(void*)*4, x_123);
x_125 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_115);
lean_ctor_set(x_125, 2, x_116);
lean_ctor_set(x_125, 3, x_117);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_123);
x_126 = 0;
lean_ctor_set(x_1, 3, x_125);
lean_ctor_set(x_1, 2, x_120);
lean_ctor_set(x_1, 1, x_119);
lean_ctor_set(x_1, 0, x_124);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_126);
return x_1;
}
}
else
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_44, 3);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_44);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_132; 
x_129 = lean_ctor_get(x_44, 3);
lean_dec(x_129);
x_130 = lean_ctor_get(x_44, 0);
lean_dec(x_130);
x_131 = 0;
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_131);
x_132 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_132);
return x_1;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; uint8_t x_137; 
x_133 = lean_ctor_get(x_44, 1);
x_134 = lean_ctor_get(x_44, 2);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_44);
x_135 = 0;
x_136 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_136, 0, x_45);
lean_ctor_set(x_136, 1, x_133);
lean_ctor_set(x_136, 2, x_134);
lean_ctor_set(x_136, 3, x_127);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_135);
x_137 = 1;
lean_ctor_set(x_1, 3, x_136);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_137);
return x_1;
}
}
else
{
uint8_t x_138; 
x_138 = lean_ctor_get_uint8(x_127, sizeof(void*)*4);
if (x_138 == 0)
{
uint8_t x_139; 
lean_free_object(x_1);
x_139 = !lean_is_exclusive(x_44);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_140 = lean_ctor_get(x_44, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_44, 0);
lean_dec(x_141);
x_142 = !lean_is_exclusive(x_127);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; 
x_143 = lean_ctor_get(x_127, 0);
x_144 = lean_ctor_get(x_127, 1);
x_145 = lean_ctor_get(x_127, 2);
x_146 = lean_ctor_get(x_127, 3);
x_147 = 1;
lean_inc(x_45);
lean_ctor_set(x_127, 3, x_45);
lean_ctor_set(x_127, 2, x_37);
lean_ctor_set(x_127, 1, x_36);
lean_ctor_set(x_127, 0, x_35);
x_148 = !lean_is_exclusive(x_45);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_149 = lean_ctor_get(x_45, 3);
lean_dec(x_149);
x_150 = lean_ctor_get(x_45, 2);
lean_dec(x_150);
x_151 = lean_ctor_get(x_45, 1);
lean_dec(x_151);
x_152 = lean_ctor_get(x_45, 0);
lean_dec(x_152);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_147);
lean_ctor_set(x_45, 3, x_146);
lean_ctor_set(x_45, 2, x_145);
lean_ctor_set(x_45, 1, x_144);
lean_ctor_set(x_45, 0, x_143);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_147);
x_153 = 0;
lean_ctor_set(x_44, 3, x_45);
lean_ctor_set(x_44, 0, x_127);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_153);
return x_44;
}
else
{
lean_object* x_154; uint8_t x_155; 
lean_dec(x_45);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_147);
x_154 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_154, 0, x_143);
lean_ctor_set(x_154, 1, x_144);
lean_ctor_set(x_154, 2, x_145);
lean_ctor_set(x_154, 3, x_146);
lean_ctor_set_uint8(x_154, sizeof(void*)*4, x_147);
x_155 = 0;
lean_ctor_set(x_44, 3, x_154);
lean_ctor_set(x_44, 0, x_127);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_155);
return x_44;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_156 = lean_ctor_get(x_127, 0);
x_157 = lean_ctor_get(x_127, 1);
x_158 = lean_ctor_get(x_127, 2);
x_159 = lean_ctor_get(x_127, 3);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_127);
x_160 = 1;
lean_inc(x_45);
x_161 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_161, 0, x_35);
lean_ctor_set(x_161, 1, x_36);
lean_ctor_set(x_161, 2, x_37);
lean_ctor_set(x_161, 3, x_45);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_162 = x_45;
} else {
 lean_dec_ref(x_45);
 x_162 = lean_box(0);
}
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_160);
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 4, 1);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_156);
lean_ctor_set(x_163, 1, x_157);
lean_ctor_set(x_163, 2, x_158);
lean_ctor_set(x_163, 3, x_159);
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_160);
x_164 = 0;
lean_ctor_set(x_44, 3, x_163);
lean_ctor_set(x_44, 0, x_161);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_164);
return x_44;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; 
x_165 = lean_ctor_get(x_44, 1);
x_166 = lean_ctor_get(x_44, 2);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_44);
x_167 = lean_ctor_get(x_127, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_127, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_127, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_127, 3);
lean_inc(x_170);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 x_171 = x_127;
} else {
 lean_dec_ref(x_127);
 x_171 = lean_box(0);
}
x_172 = 1;
lean_inc(x_45);
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(1, 4, 1);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_35);
lean_ctor_set(x_173, 1, x_36);
lean_ctor_set(x_173, 2, x_37);
lean_ctor_set(x_173, 3, x_45);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_174 = x_45;
} else {
 lean_dec_ref(x_45);
 x_174 = lean_box(0);
}
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_172);
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 4, 1);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_167);
lean_ctor_set(x_175, 1, x_168);
lean_ctor_set(x_175, 2, x_169);
lean_ctor_set(x_175, 3, x_170);
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_172);
x_176 = 0;
x_177 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_165);
lean_ctor_set(x_177, 2, x_166);
lean_ctor_set(x_177, 3, x_175);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_176);
return x_177;
}
}
else
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_44);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_ctor_get(x_44, 3);
lean_dec(x_179);
x_180 = lean_ctor_get(x_44, 0);
lean_dec(x_180);
x_181 = !lean_is_exclusive(x_45);
if (x_181 == 0)
{
uint8_t x_182; uint8_t x_183; 
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_138);
x_182 = 0;
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_182);
x_183 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; uint8_t x_190; 
x_184 = lean_ctor_get(x_45, 0);
x_185 = lean_ctor_get(x_45, 1);
x_186 = lean_ctor_get(x_45, 2);
x_187 = lean_ctor_get(x_45, 3);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_45);
x_188 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_188, 0, x_184);
lean_ctor_set(x_188, 1, x_185);
lean_ctor_set(x_188, 2, x_186);
lean_ctor_set(x_188, 3, x_187);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_138);
x_189 = 0;
lean_ctor_set(x_44, 0, x_188);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_189);
x_190 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_190);
return x_1;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; uint8_t x_201; 
x_191 = lean_ctor_get(x_44, 1);
x_192 = lean_ctor_get(x_44, 2);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_44);
x_193 = lean_ctor_get(x_45, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_45, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_45, 2);
lean_inc(x_195);
x_196 = lean_ctor_get(x_45, 3);
lean_inc(x_196);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_197 = x_45;
} else {
 lean_dec_ref(x_45);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 4, 1);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_193);
lean_ctor_set(x_198, 1, x_194);
lean_ctor_set(x_198, 2, x_195);
lean_ctor_set(x_198, 3, x_196);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_138);
x_199 = 0;
x_200 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_191);
lean_ctor_set(x_200, 2, x_192);
lean_ctor_set(x_200, 3, x_127);
lean_ctor_set_uint8(x_200, sizeof(void*)*4, x_199);
x_201 = 1;
lean_ctor_set(x_1, 3, x_200);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_201);
return x_1;
}
}
}
}
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_37);
lean_dec(x_36);
x_202 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
}
}
else
{
uint8_t x_203; 
x_203 = l_Std_RBNode_isRed___rarg(x_35);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__2(x_35, x_2, x_3);
x_205 = 1;
lean_ctor_set(x_1, 0, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_205);
return x_1;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__2(x_35, x_2, x_3);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_206, 3);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_206);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; uint8_t x_213; 
x_210 = lean_ctor_get(x_206, 3);
lean_dec(x_210);
x_211 = lean_ctor_get(x_206, 0);
lean_dec(x_211);
x_212 = 0;
lean_ctor_set(x_206, 0, x_208);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_212);
x_213 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_213);
return x_1;
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_206, 1);
x_215 = lean_ctor_get(x_206, 2);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_206);
x_216 = 0;
x_217 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_217, 0, x_208);
lean_ctor_set(x_217, 1, x_214);
lean_ctor_set(x_217, 2, x_215);
lean_ctor_set(x_217, 3, x_208);
lean_ctor_set_uint8(x_217, sizeof(void*)*4, x_216);
x_218 = 1;
lean_ctor_set(x_1, 0, x_217);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_218);
return x_1;
}
}
else
{
uint8_t x_219; 
x_219 = lean_ctor_get_uint8(x_208, sizeof(void*)*4);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_206);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_221 = lean_ctor_get(x_206, 1);
x_222 = lean_ctor_get(x_206, 2);
x_223 = lean_ctor_get(x_206, 3);
lean_dec(x_223);
x_224 = lean_ctor_get(x_206, 0);
lean_dec(x_224);
x_225 = !lean_is_exclusive(x_208);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_231; 
x_226 = lean_ctor_get(x_208, 0);
x_227 = lean_ctor_get(x_208, 1);
x_228 = lean_ctor_get(x_208, 2);
x_229 = lean_ctor_get(x_208, 3);
x_230 = 1;
lean_ctor_set(x_208, 3, x_226);
lean_ctor_set(x_208, 2, x_222);
lean_ctor_set(x_208, 1, x_221);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_230);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_229);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_230);
x_231 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_208);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_231);
return x_1;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; uint8_t x_238; 
x_232 = lean_ctor_get(x_208, 0);
x_233 = lean_ctor_get(x_208, 1);
x_234 = lean_ctor_get(x_208, 2);
x_235 = lean_ctor_get(x_208, 3);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_208);
x_236 = 1;
x_237 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_237, 0, x_207);
lean_ctor_set(x_237, 1, x_221);
lean_ctor_set(x_237, 2, x_222);
lean_ctor_set(x_237, 3, x_232);
lean_ctor_set_uint8(x_237, sizeof(void*)*4, x_236);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_235);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_236);
x_238 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_234);
lean_ctor_set(x_1, 1, x_233);
lean_ctor_set(x_1, 0, x_237);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_238);
return x_1;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_239 = lean_ctor_get(x_206, 1);
x_240 = lean_ctor_get(x_206, 2);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_206);
x_241 = lean_ctor_get(x_208, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_208, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_208, 2);
lean_inc(x_243);
x_244 = lean_ctor_get(x_208, 3);
lean_inc(x_244);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 lean_ctor_release(x_208, 3);
 x_245 = x_208;
} else {
 lean_dec_ref(x_208);
 x_245 = lean_box(0);
}
x_246 = 1;
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(1, 4, 1);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_207);
lean_ctor_set(x_247, 1, x_239);
lean_ctor_set(x_247, 2, x_240);
lean_ctor_set(x_247, 3, x_241);
lean_ctor_set_uint8(x_247, sizeof(void*)*4, x_246);
x_248 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_248, 0, x_244);
lean_ctor_set(x_248, 1, x_36);
lean_ctor_set(x_248, 2, x_37);
lean_ctor_set(x_248, 3, x_38);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_246);
x_249 = 0;
lean_ctor_set(x_1, 3, x_248);
lean_ctor_set(x_1, 2, x_243);
lean_ctor_set(x_1, 1, x_242);
lean_ctor_set(x_1, 0, x_247);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_249);
return x_1;
}
}
else
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_206);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_254; 
x_251 = lean_ctor_get(x_206, 3);
lean_dec(x_251);
x_252 = lean_ctor_get(x_206, 0);
lean_dec(x_252);
x_253 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_253);
x_254 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_254);
return x_1;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_255 = lean_ctor_get(x_206, 1);
x_256 = lean_ctor_get(x_206, 2);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_206);
x_257 = 0;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_207);
lean_ctor_set(x_258, 1, x_255);
lean_ctor_set(x_258, 2, x_256);
lean_ctor_set(x_258, 3, x_208);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
x_259 = 1;
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
else
{
uint8_t x_260; 
x_260 = lean_ctor_get_uint8(x_207, sizeof(void*)*4);
if (x_260 == 0)
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_206);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_262 = lean_ctor_get(x_206, 1);
x_263 = lean_ctor_get(x_206, 2);
x_264 = lean_ctor_get(x_206, 3);
x_265 = lean_ctor_get(x_206, 0);
lean_dec(x_265);
x_266 = !lean_is_exclusive(x_207);
if (x_266 == 0)
{
uint8_t x_267; uint8_t x_268; 
x_267 = 1;
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_267);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_267);
x_268 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_207);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_268);
return x_1;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; uint8_t x_275; 
x_269 = lean_ctor_get(x_207, 0);
x_270 = lean_ctor_get(x_207, 1);
x_271 = lean_ctor_get(x_207, 2);
x_272 = lean_ctor_get(x_207, 3);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_207);
x_273 = 1;
x_274 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_274, 0, x_269);
lean_ctor_set(x_274, 1, x_270);
lean_ctor_set(x_274, 2, x_271);
lean_ctor_set(x_274, 3, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*4, x_273);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_273);
x_275 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_274);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_275);
return x_1;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_276 = lean_ctor_get(x_206, 1);
x_277 = lean_ctor_get(x_206, 2);
x_278 = lean_ctor_get(x_206, 3);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_206);
x_279 = lean_ctor_get(x_207, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_207, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_207, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_207, 3);
lean_inc(x_282);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_283 = x_207;
} else {
 lean_dec_ref(x_207);
 x_283 = lean_box(0);
}
x_284 = 1;
if (lean_is_scalar(x_283)) {
 x_285 = lean_alloc_ctor(1, 4, 1);
} else {
 x_285 = x_283;
}
lean_ctor_set(x_285, 0, x_279);
lean_ctor_set(x_285, 1, x_280);
lean_ctor_set(x_285, 2, x_281);
lean_ctor_set(x_285, 3, x_282);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_284);
x_286 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_286, 0, x_278);
lean_ctor_set(x_286, 1, x_36);
lean_ctor_set(x_286, 2, x_37);
lean_ctor_set(x_286, 3, x_38);
lean_ctor_set_uint8(x_286, sizeof(void*)*4, x_284);
x_287 = 0;
lean_ctor_set(x_1, 3, x_286);
lean_ctor_set(x_1, 2, x_277);
lean_ctor_set(x_1, 1, x_276);
lean_ctor_set(x_1, 0, x_285);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_287);
return x_1;
}
}
else
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_206, 3);
lean_inc(x_288);
if (lean_obj_tag(x_288) == 0)
{
uint8_t x_289; 
x_289 = !lean_is_exclusive(x_206);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_293; 
x_290 = lean_ctor_get(x_206, 3);
lean_dec(x_290);
x_291 = lean_ctor_get(x_206, 0);
lean_dec(x_291);
x_292 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_292);
x_293 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_293);
return x_1;
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_206, 1);
x_295 = lean_ctor_get(x_206, 2);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_206);
x_296 = 0;
x_297 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_297, 0, x_207);
lean_ctor_set(x_297, 1, x_294);
lean_ctor_set(x_297, 2, x_295);
lean_ctor_set(x_297, 3, x_288);
lean_ctor_set_uint8(x_297, sizeof(void*)*4, x_296);
x_298 = 1;
lean_ctor_set(x_1, 0, x_297);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_298);
return x_1;
}
}
else
{
uint8_t x_299; 
x_299 = lean_ctor_get_uint8(x_288, sizeof(void*)*4);
if (x_299 == 0)
{
uint8_t x_300; 
lean_free_object(x_1);
x_300 = !lean_is_exclusive(x_206);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_301 = lean_ctor_get(x_206, 1);
x_302 = lean_ctor_get(x_206, 2);
x_303 = lean_ctor_get(x_206, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_206, 0);
lean_dec(x_304);
x_305 = !lean_is_exclusive(x_288);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_311; 
x_306 = lean_ctor_get(x_288, 0);
x_307 = lean_ctor_get(x_288, 1);
x_308 = lean_ctor_get(x_288, 2);
x_309 = lean_ctor_get(x_288, 3);
x_310 = 1;
lean_inc(x_207);
lean_ctor_set(x_288, 3, x_306);
lean_ctor_set(x_288, 2, x_302);
lean_ctor_set(x_288, 1, x_301);
lean_ctor_set(x_288, 0, x_207);
x_311 = !lean_is_exclusive(x_207);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_312 = lean_ctor_get(x_207, 3);
lean_dec(x_312);
x_313 = lean_ctor_get(x_207, 2);
lean_dec(x_313);
x_314 = lean_ctor_get(x_207, 1);
lean_dec(x_314);
x_315 = lean_ctor_get(x_207, 0);
lean_dec(x_315);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
lean_ctor_set(x_207, 3, x_38);
lean_ctor_set(x_207, 2, x_37);
lean_ctor_set(x_207, 1, x_36);
lean_ctor_set(x_207, 0, x_309);
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_310);
x_316 = 0;
lean_ctor_set(x_206, 3, x_207);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_316);
return x_206;
}
else
{
lean_object* x_317; uint8_t x_318; 
lean_dec(x_207);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
x_317 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_36);
lean_ctor_set(x_317, 2, x_37);
lean_ctor_set(x_317, 3, x_38);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_310);
x_318 = 0;
lean_ctor_set(x_206, 3, x_317);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_318);
return x_206;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_319 = lean_ctor_get(x_288, 0);
x_320 = lean_ctor_get(x_288, 1);
x_321 = lean_ctor_get(x_288, 2);
x_322 = lean_ctor_get(x_288, 3);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_288);
x_323 = 1;
lean_inc(x_207);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_207);
lean_ctor_set(x_324, 1, x_301);
lean_ctor_set(x_324, 2, x_302);
lean_ctor_set(x_324, 3, x_319);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_325 = x_207;
} else {
 lean_dec_ref(x_207);
 x_325 = lean_box(0);
}
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_323);
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 4, 1);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_322);
lean_ctor_set(x_326, 1, x_36);
lean_ctor_set(x_326, 2, x_37);
lean_ctor_set(x_326, 3, x_38);
lean_ctor_set_uint8(x_326, sizeof(void*)*4, x_323);
x_327 = 0;
lean_ctor_set(x_206, 3, x_326);
lean_ctor_set(x_206, 2, x_321);
lean_ctor_set(x_206, 1, x_320);
lean_ctor_set(x_206, 0, x_324);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_327);
return x_206;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; 
x_328 = lean_ctor_get(x_206, 1);
x_329 = lean_ctor_get(x_206, 2);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_206);
x_330 = lean_ctor_get(x_288, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_288, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_288, 2);
lean_inc(x_332);
x_333 = lean_ctor_get(x_288, 3);
lean_inc(x_333);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 lean_ctor_release(x_288, 2);
 lean_ctor_release(x_288, 3);
 x_334 = x_288;
} else {
 lean_dec_ref(x_288);
 x_334 = lean_box(0);
}
x_335 = 1;
lean_inc(x_207);
if (lean_is_scalar(x_334)) {
 x_336 = lean_alloc_ctor(1, 4, 1);
} else {
 x_336 = x_334;
}
lean_ctor_set(x_336, 0, x_207);
lean_ctor_set(x_336, 1, x_328);
lean_ctor_set(x_336, 2, x_329);
lean_ctor_set(x_336, 3, x_330);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_337 = x_207;
} else {
 lean_dec_ref(x_207);
 x_337 = lean_box(0);
}
lean_ctor_set_uint8(x_336, sizeof(void*)*4, x_335);
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_36);
lean_ctor_set(x_338, 2, x_37);
lean_ctor_set(x_338, 3, x_38);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_335);
x_339 = 0;
x_340 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_340, 0, x_336);
lean_ctor_set(x_340, 1, x_331);
lean_ctor_set(x_340, 2, x_332);
lean_ctor_set(x_340, 3, x_338);
lean_ctor_set_uint8(x_340, sizeof(void*)*4, x_339);
return x_340;
}
}
else
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_206);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_342 = lean_ctor_get(x_206, 3);
lean_dec(x_342);
x_343 = lean_ctor_get(x_206, 0);
lean_dec(x_343);
x_344 = !lean_is_exclusive(x_207);
if (x_344 == 0)
{
uint8_t x_345; uint8_t x_346; 
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_299);
x_345 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_345);
x_346 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_346);
return x_1;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; uint8_t x_353; 
x_347 = lean_ctor_get(x_207, 0);
x_348 = lean_ctor_get(x_207, 1);
x_349 = lean_ctor_get(x_207, 2);
x_350 = lean_ctor_get(x_207, 3);
lean_inc(x_350);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_207);
x_351 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_351, 0, x_347);
lean_ctor_set(x_351, 1, x_348);
lean_ctor_set(x_351, 2, x_349);
lean_ctor_set(x_351, 3, x_350);
lean_ctor_set_uint8(x_351, sizeof(void*)*4, x_299);
x_352 = 0;
lean_ctor_set(x_206, 0, x_351);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_352);
x_353 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_353);
return x_1;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; uint8_t x_364; 
x_354 = lean_ctor_get(x_206, 1);
x_355 = lean_ctor_get(x_206, 2);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_206);
x_356 = lean_ctor_get(x_207, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_207, 1);
lean_inc(x_357);
x_358 = lean_ctor_get(x_207, 2);
lean_inc(x_358);
x_359 = lean_ctor_get(x_207, 3);
lean_inc(x_359);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_360 = x_207;
} else {
 lean_dec_ref(x_207);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 4, 1);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_356);
lean_ctor_set(x_361, 1, x_357);
lean_ctor_set(x_361, 2, x_358);
lean_ctor_set(x_361, 3, x_359);
lean_ctor_set_uint8(x_361, sizeof(void*)*4, x_299);
x_362 = 0;
x_363 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_354);
lean_ctor_set(x_363, 2, x_355);
lean_ctor_set(x_363, 3, x_288);
lean_ctor_set_uint8(x_363, sizeof(void*)*4, x_362);
x_364 = 1;
lean_ctor_set(x_1, 0, x_363);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_364);
return x_1;
}
}
}
}
}
}
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_365 = lean_ctor_get(x_1, 0);
x_366 = lean_ctor_get(x_1, 1);
x_367 = lean_ctor_get(x_1, 2);
x_368 = lean_ctor_get(x_1, 3);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_1);
x_369 = lean_nat_dec_lt(x_2, x_366);
if (x_369 == 0)
{
uint8_t x_370; 
x_370 = lean_nat_dec_eq(x_2, x_366);
if (x_370 == 0)
{
uint8_t x_371; 
x_371 = l_Std_RBNode_isRed___rarg(x_368);
if (x_371 == 0)
{
lean_object* x_372; uint8_t x_373; lean_object* x_374; 
x_372 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__2(x_368, x_2, x_3);
x_373 = 1;
x_374 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_374, 0, x_365);
lean_ctor_set(x_374, 1, x_366);
lean_ctor_set(x_374, 2, x_367);
lean_ctor_set(x_374, 3, x_372);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_373);
return x_374;
}
else
{
lean_object* x_375; lean_object* x_376; 
x_375 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__2(x_368, x_2, x_3);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; 
x_377 = lean_ctor_get(x_375, 3);
lean_inc(x_377);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; 
x_378 = lean_ctor_get(x_375, 1);
lean_inc(x_378);
x_379 = lean_ctor_get(x_375, 2);
lean_inc(x_379);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_380 = x_375;
} else {
 lean_dec_ref(x_375);
 x_380 = lean_box(0);
}
x_381 = 0;
if (lean_is_scalar(x_380)) {
 x_382 = lean_alloc_ctor(1, 4, 1);
} else {
 x_382 = x_380;
}
lean_ctor_set(x_382, 0, x_377);
lean_ctor_set(x_382, 1, x_378);
lean_ctor_set(x_382, 2, x_379);
lean_ctor_set(x_382, 3, x_377);
lean_ctor_set_uint8(x_382, sizeof(void*)*4, x_381);
x_383 = 1;
x_384 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_384, 0, x_365);
lean_ctor_set(x_384, 1, x_366);
lean_ctor_set(x_384, 2, x_367);
lean_ctor_set(x_384, 3, x_382);
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_383);
return x_384;
}
else
{
uint8_t x_385; 
x_385 = lean_ctor_get_uint8(x_377, sizeof(void*)*4);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; 
x_386 = lean_ctor_get(x_375, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_375, 2);
lean_inc(x_387);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_388 = x_375;
} else {
 lean_dec_ref(x_375);
 x_388 = lean_box(0);
}
x_389 = lean_ctor_get(x_377, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_377, 1);
lean_inc(x_390);
x_391 = lean_ctor_get(x_377, 2);
lean_inc(x_391);
x_392 = lean_ctor_get(x_377, 3);
lean_inc(x_392);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_393 = x_377;
} else {
 lean_dec_ref(x_377);
 x_393 = lean_box(0);
}
x_394 = 1;
if (lean_is_scalar(x_393)) {
 x_395 = lean_alloc_ctor(1, 4, 1);
} else {
 x_395 = x_393;
}
lean_ctor_set(x_395, 0, x_365);
lean_ctor_set(x_395, 1, x_366);
lean_ctor_set(x_395, 2, x_367);
lean_ctor_set(x_395, 3, x_376);
lean_ctor_set_uint8(x_395, sizeof(void*)*4, x_394);
if (lean_is_scalar(x_388)) {
 x_396 = lean_alloc_ctor(1, 4, 1);
} else {
 x_396 = x_388;
}
lean_ctor_set(x_396, 0, x_389);
lean_ctor_set(x_396, 1, x_390);
lean_ctor_set(x_396, 2, x_391);
lean_ctor_set(x_396, 3, x_392);
lean_ctor_set_uint8(x_396, sizeof(void*)*4, x_394);
x_397 = 0;
x_398 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_386);
lean_ctor_set(x_398, 2, x_387);
lean_ctor_set(x_398, 3, x_396);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_397);
return x_398;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; 
x_399 = lean_ctor_get(x_375, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_375, 2);
lean_inc(x_400);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_401 = x_375;
} else {
 lean_dec_ref(x_375);
 x_401 = lean_box(0);
}
x_402 = 0;
if (lean_is_scalar(x_401)) {
 x_403 = lean_alloc_ctor(1, 4, 1);
} else {
 x_403 = x_401;
}
lean_ctor_set(x_403, 0, x_376);
lean_ctor_set(x_403, 1, x_399);
lean_ctor_set(x_403, 2, x_400);
lean_ctor_set(x_403, 3, x_377);
lean_ctor_set_uint8(x_403, sizeof(void*)*4, x_402);
x_404 = 1;
x_405 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_405, 0, x_365);
lean_ctor_set(x_405, 1, x_366);
lean_ctor_set(x_405, 2, x_367);
lean_ctor_set(x_405, 3, x_403);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_404);
return x_405;
}
}
}
else
{
uint8_t x_406; 
x_406 = lean_ctor_get_uint8(x_376, sizeof(void*)*4);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; lean_object* x_420; 
x_407 = lean_ctor_get(x_375, 1);
lean_inc(x_407);
x_408 = lean_ctor_get(x_375, 2);
lean_inc(x_408);
x_409 = lean_ctor_get(x_375, 3);
lean_inc(x_409);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_410 = x_375;
} else {
 lean_dec_ref(x_375);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_376, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_376, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_376, 2);
lean_inc(x_413);
x_414 = lean_ctor_get(x_376, 3);
lean_inc(x_414);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_415 = x_376;
} else {
 lean_dec_ref(x_376);
 x_415 = lean_box(0);
}
x_416 = 1;
if (lean_is_scalar(x_415)) {
 x_417 = lean_alloc_ctor(1, 4, 1);
} else {
 x_417 = x_415;
}
lean_ctor_set(x_417, 0, x_365);
lean_ctor_set(x_417, 1, x_366);
lean_ctor_set(x_417, 2, x_367);
lean_ctor_set(x_417, 3, x_411);
lean_ctor_set_uint8(x_417, sizeof(void*)*4, x_416);
if (lean_is_scalar(x_410)) {
 x_418 = lean_alloc_ctor(1, 4, 1);
} else {
 x_418 = x_410;
}
lean_ctor_set(x_418, 0, x_414);
lean_ctor_set(x_418, 1, x_407);
lean_ctor_set(x_418, 2, x_408);
lean_ctor_set(x_418, 3, x_409);
lean_ctor_set_uint8(x_418, sizeof(void*)*4, x_416);
x_419 = 0;
x_420 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_420, 0, x_417);
lean_ctor_set(x_420, 1, x_412);
lean_ctor_set(x_420, 2, x_413);
lean_ctor_set(x_420, 3, x_418);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_419);
return x_420;
}
else
{
lean_object* x_421; 
x_421 = lean_ctor_get(x_375, 3);
lean_inc(x_421);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; 
x_422 = lean_ctor_get(x_375, 1);
lean_inc(x_422);
x_423 = lean_ctor_get(x_375, 2);
lean_inc(x_423);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_424 = x_375;
} else {
 lean_dec_ref(x_375);
 x_424 = lean_box(0);
}
x_425 = 0;
if (lean_is_scalar(x_424)) {
 x_426 = lean_alloc_ctor(1, 4, 1);
} else {
 x_426 = x_424;
}
lean_ctor_set(x_426, 0, x_376);
lean_ctor_set(x_426, 1, x_422);
lean_ctor_set(x_426, 2, x_423);
lean_ctor_set(x_426, 3, x_421);
lean_ctor_set_uint8(x_426, sizeof(void*)*4, x_425);
x_427 = 1;
x_428 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_428, 0, x_365);
lean_ctor_set(x_428, 1, x_366);
lean_ctor_set(x_428, 2, x_367);
lean_ctor_set(x_428, 3, x_426);
lean_ctor_set_uint8(x_428, sizeof(void*)*4, x_427);
return x_428;
}
else
{
uint8_t x_429; 
x_429 = lean_ctor_get_uint8(x_421, sizeof(void*)*4);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; 
x_430 = lean_ctor_get(x_375, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_375, 2);
lean_inc(x_431);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_432 = x_375;
} else {
 lean_dec_ref(x_375);
 x_432 = lean_box(0);
}
x_433 = lean_ctor_get(x_421, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_421, 1);
lean_inc(x_434);
x_435 = lean_ctor_get(x_421, 2);
lean_inc(x_435);
x_436 = lean_ctor_get(x_421, 3);
lean_inc(x_436);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 lean_ctor_release(x_421, 2);
 lean_ctor_release(x_421, 3);
 x_437 = x_421;
} else {
 lean_dec_ref(x_421);
 x_437 = lean_box(0);
}
x_438 = 1;
lean_inc(x_376);
if (lean_is_scalar(x_437)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_437;
}
lean_ctor_set(x_439, 0, x_365);
lean_ctor_set(x_439, 1, x_366);
lean_ctor_set(x_439, 2, x_367);
lean_ctor_set(x_439, 3, x_376);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_440 = x_376;
} else {
 lean_dec_ref(x_376);
 x_440 = lean_box(0);
}
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 4, 1);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_433);
lean_ctor_set(x_441, 1, x_434);
lean_ctor_set(x_441, 2, x_435);
lean_ctor_set(x_441, 3, x_436);
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_438);
x_442 = 0;
if (lean_is_scalar(x_432)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_432;
}
lean_ctor_set(x_443, 0, x_439);
lean_ctor_set(x_443, 1, x_430);
lean_ctor_set(x_443, 2, x_431);
lean_ctor_set(x_443, 3, x_441);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_442);
return x_443;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; 
x_444 = lean_ctor_get(x_375, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_375, 2);
lean_inc(x_445);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_446 = x_375;
} else {
 lean_dec_ref(x_375);
 x_446 = lean_box(0);
}
x_447 = lean_ctor_get(x_376, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_376, 1);
lean_inc(x_448);
x_449 = lean_ctor_get(x_376, 2);
lean_inc(x_449);
x_450 = lean_ctor_get(x_376, 3);
lean_inc(x_450);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_451 = x_376;
} else {
 lean_dec_ref(x_376);
 x_451 = lean_box(0);
}
if (lean_is_scalar(x_451)) {
 x_452 = lean_alloc_ctor(1, 4, 1);
} else {
 x_452 = x_451;
}
lean_ctor_set(x_452, 0, x_447);
lean_ctor_set(x_452, 1, x_448);
lean_ctor_set(x_452, 2, x_449);
lean_ctor_set(x_452, 3, x_450);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_429);
x_453 = 0;
if (lean_is_scalar(x_446)) {
 x_454 = lean_alloc_ctor(1, 4, 1);
} else {
 x_454 = x_446;
}
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_444);
lean_ctor_set(x_454, 2, x_445);
lean_ctor_set(x_454, 3, x_421);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_453);
x_455 = 1;
x_456 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_456, 0, x_365);
lean_ctor_set(x_456, 1, x_366);
lean_ctor_set(x_456, 2, x_367);
lean_ctor_set(x_456, 3, x_454);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_455);
return x_456;
}
}
}
}
}
}
else
{
uint8_t x_457; lean_object* x_458; 
lean_dec(x_367);
lean_dec(x_366);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_365);
lean_ctor_set(x_458, 1, x_2);
lean_ctor_set(x_458, 2, x_3);
lean_ctor_set(x_458, 3, x_368);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
}
else
{
uint8_t x_459; 
x_459 = l_Std_RBNode_isRed___rarg(x_365);
if (x_459 == 0)
{
lean_object* x_460; uint8_t x_461; lean_object* x_462; 
x_460 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__2(x_365, x_2, x_3);
x_461 = 1;
x_462 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_366);
lean_ctor_set(x_462, 2, x_367);
lean_ctor_set(x_462, 3, x_368);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
return x_462;
}
else
{
lean_object* x_463; lean_object* x_464; 
x_463 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__2(x_365, x_2, x_3);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; 
x_465 = lean_ctor_get(x_463, 3);
lean_inc(x_465);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; lean_object* x_470; uint8_t x_471; lean_object* x_472; 
x_466 = lean_ctor_get(x_463, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_463, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_468 = x_463;
} else {
 lean_dec_ref(x_463);
 x_468 = lean_box(0);
}
x_469 = 0;
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(1, 4, 1);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_465);
lean_ctor_set(x_470, 1, x_466);
lean_ctor_set(x_470, 2, x_467);
lean_ctor_set(x_470, 3, x_465);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_469);
x_471 = 1;
x_472 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_366);
lean_ctor_set(x_472, 2, x_367);
lean_ctor_set(x_472, 3, x_368);
lean_ctor_set_uint8(x_472, sizeof(void*)*4, x_471);
return x_472;
}
else
{
uint8_t x_473; 
x_473 = lean_ctor_get_uint8(x_465, sizeof(void*)*4);
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; 
x_474 = lean_ctor_get(x_463, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_463, 2);
lean_inc(x_475);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_476 = x_463;
} else {
 lean_dec_ref(x_463);
 x_476 = lean_box(0);
}
x_477 = lean_ctor_get(x_465, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_465, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_465, 2);
lean_inc(x_479);
x_480 = lean_ctor_get(x_465, 3);
lean_inc(x_480);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 lean_ctor_release(x_465, 2);
 lean_ctor_release(x_465, 3);
 x_481 = x_465;
} else {
 lean_dec_ref(x_465);
 x_481 = lean_box(0);
}
x_482 = 1;
if (lean_is_scalar(x_481)) {
 x_483 = lean_alloc_ctor(1, 4, 1);
} else {
 x_483 = x_481;
}
lean_ctor_set(x_483, 0, x_464);
lean_ctor_set(x_483, 1, x_474);
lean_ctor_set(x_483, 2, x_475);
lean_ctor_set(x_483, 3, x_477);
lean_ctor_set_uint8(x_483, sizeof(void*)*4, x_482);
if (lean_is_scalar(x_476)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_476;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_366);
lean_ctor_set(x_484, 2, x_367);
lean_ctor_set(x_484, 3, x_368);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_482);
x_485 = 0;
x_486 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_478);
lean_ctor_set(x_486, 2, x_479);
lean_ctor_set(x_486, 3, x_484);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_485);
return x_486;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; lean_object* x_491; uint8_t x_492; lean_object* x_493; 
x_487 = lean_ctor_get(x_463, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_463, 2);
lean_inc(x_488);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_489 = x_463;
} else {
 lean_dec_ref(x_463);
 x_489 = lean_box(0);
}
x_490 = 0;
if (lean_is_scalar(x_489)) {
 x_491 = lean_alloc_ctor(1, 4, 1);
} else {
 x_491 = x_489;
}
lean_ctor_set(x_491, 0, x_464);
lean_ctor_set(x_491, 1, x_487);
lean_ctor_set(x_491, 2, x_488);
lean_ctor_set(x_491, 3, x_465);
lean_ctor_set_uint8(x_491, sizeof(void*)*4, x_490);
x_492 = 1;
x_493 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_366);
lean_ctor_set(x_493, 2, x_367);
lean_ctor_set(x_493, 3, x_368);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_492);
return x_493;
}
}
}
else
{
uint8_t x_494; 
x_494 = lean_ctor_get_uint8(x_464, sizeof(void*)*4);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; lean_object* x_508; 
x_495 = lean_ctor_get(x_463, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_463, 2);
lean_inc(x_496);
x_497 = lean_ctor_get(x_463, 3);
lean_inc(x_497);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_498 = x_463;
} else {
 lean_dec_ref(x_463);
 x_498 = lean_box(0);
}
x_499 = lean_ctor_get(x_464, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_464, 1);
lean_inc(x_500);
x_501 = lean_ctor_get(x_464, 2);
lean_inc(x_501);
x_502 = lean_ctor_get(x_464, 3);
lean_inc(x_502);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_503 = x_464;
} else {
 lean_dec_ref(x_464);
 x_503 = lean_box(0);
}
x_504 = 1;
if (lean_is_scalar(x_503)) {
 x_505 = lean_alloc_ctor(1, 4, 1);
} else {
 x_505 = x_503;
}
lean_ctor_set(x_505, 0, x_499);
lean_ctor_set(x_505, 1, x_500);
lean_ctor_set(x_505, 2, x_501);
lean_ctor_set(x_505, 3, x_502);
lean_ctor_set_uint8(x_505, sizeof(void*)*4, x_504);
if (lean_is_scalar(x_498)) {
 x_506 = lean_alloc_ctor(1, 4, 1);
} else {
 x_506 = x_498;
}
lean_ctor_set(x_506, 0, x_497);
lean_ctor_set(x_506, 1, x_366);
lean_ctor_set(x_506, 2, x_367);
lean_ctor_set(x_506, 3, x_368);
lean_ctor_set_uint8(x_506, sizeof(void*)*4, x_504);
x_507 = 0;
x_508 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_495);
lean_ctor_set(x_508, 2, x_496);
lean_ctor_set(x_508, 3, x_506);
lean_ctor_set_uint8(x_508, sizeof(void*)*4, x_507);
return x_508;
}
else
{
lean_object* x_509; 
x_509 = lean_ctor_get(x_463, 3);
lean_inc(x_509);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; lean_object* x_514; uint8_t x_515; lean_object* x_516; 
x_510 = lean_ctor_get(x_463, 1);
lean_inc(x_510);
x_511 = lean_ctor_get(x_463, 2);
lean_inc(x_511);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_512 = x_463;
} else {
 lean_dec_ref(x_463);
 x_512 = lean_box(0);
}
x_513 = 0;
if (lean_is_scalar(x_512)) {
 x_514 = lean_alloc_ctor(1, 4, 1);
} else {
 x_514 = x_512;
}
lean_ctor_set(x_514, 0, x_464);
lean_ctor_set(x_514, 1, x_510);
lean_ctor_set(x_514, 2, x_511);
lean_ctor_set(x_514, 3, x_509);
lean_ctor_set_uint8(x_514, sizeof(void*)*4, x_513);
x_515 = 1;
x_516 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_366);
lean_ctor_set(x_516, 2, x_367);
lean_ctor_set(x_516, 3, x_368);
lean_ctor_set_uint8(x_516, sizeof(void*)*4, x_515);
return x_516;
}
else
{
uint8_t x_517; 
x_517 = lean_ctor_get_uint8(x_509, sizeof(void*)*4);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; uint8_t x_530; lean_object* x_531; 
x_518 = lean_ctor_get(x_463, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_463, 2);
lean_inc(x_519);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_520 = x_463;
} else {
 lean_dec_ref(x_463);
 x_520 = lean_box(0);
}
x_521 = lean_ctor_get(x_509, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_509, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_509, 2);
lean_inc(x_523);
x_524 = lean_ctor_get(x_509, 3);
lean_inc(x_524);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 lean_ctor_release(x_509, 2);
 lean_ctor_release(x_509, 3);
 x_525 = x_509;
} else {
 lean_dec_ref(x_509);
 x_525 = lean_box(0);
}
x_526 = 1;
lean_inc(x_464);
if (lean_is_scalar(x_525)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_525;
}
lean_ctor_set(x_527, 0, x_464);
lean_ctor_set(x_527, 1, x_518);
lean_ctor_set(x_527, 2, x_519);
lean_ctor_set(x_527, 3, x_521);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_528 = x_464;
} else {
 lean_dec_ref(x_464);
 x_528 = lean_box(0);
}
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(1, 4, 1);
} else {
 x_529 = x_528;
}
lean_ctor_set(x_529, 0, x_524);
lean_ctor_set(x_529, 1, x_366);
lean_ctor_set(x_529, 2, x_367);
lean_ctor_set(x_529, 3, x_368);
lean_ctor_set_uint8(x_529, sizeof(void*)*4, x_526);
x_530 = 0;
if (lean_is_scalar(x_520)) {
 x_531 = lean_alloc_ctor(1, 4, 1);
} else {
 x_531 = x_520;
}
lean_ctor_set(x_531, 0, x_527);
lean_ctor_set(x_531, 1, x_522);
lean_ctor_set(x_531, 2, x_523);
lean_ctor_set(x_531, 3, x_529);
lean_ctor_set_uint8(x_531, sizeof(void*)*4, x_530);
return x_531;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; uint8_t x_543; lean_object* x_544; 
x_532 = lean_ctor_get(x_463, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_463, 2);
lean_inc(x_533);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_534 = x_463;
} else {
 lean_dec_ref(x_463);
 x_534 = lean_box(0);
}
x_535 = lean_ctor_get(x_464, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_464, 1);
lean_inc(x_536);
x_537 = lean_ctor_get(x_464, 2);
lean_inc(x_537);
x_538 = lean_ctor_get(x_464, 3);
lean_inc(x_538);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_539 = x_464;
} else {
 lean_dec_ref(x_464);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 4, 1);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_535);
lean_ctor_set(x_540, 1, x_536);
lean_ctor_set(x_540, 2, x_537);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_517);
x_541 = 0;
if (lean_is_scalar(x_534)) {
 x_542 = lean_alloc_ctor(1, 4, 1);
} else {
 x_542 = x_534;
}
lean_ctor_set(x_542, 0, x_540);
lean_ctor_set(x_542, 1, x_532);
lean_ctor_set(x_542, 2, x_533);
lean_ctor_set(x_542, 3, x_509);
lean_ctor_set_uint8(x_542, sizeof(void*)*4, x_541);
x_543 = 1;
x_544 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_366);
lean_ctor_set(x_544, 2, x_367);
lean_ctor_set(x_544, 3, x_368);
lean_ctor_set_uint8(x_544, sizeof(void*)*4, x_543);
return x_544;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__2(x_1, x_2, x_3);
x_7 = l_Std_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_traceMsg", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("] ", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Util_Trace_0__Lean_addTraceOptions(x_12);
x_15 = lean_st_ref_take(x_8, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_16, 3);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__2;
x_24 = l_Lean_Name_append(x_1, x_23);
x_25 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_25, 0, x_1);
x_26 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__4;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__6;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_14);
x_31 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__8;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_10);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Std_PersistentArray_push___rarg(x_22, x_34);
lean_ctor_set(x_17, 0, x_35);
x_36 = lean_st_ref_set(x_8, x_16, x_18);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_43 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
x_44 = lean_ctor_get(x_17, 0);
lean_inc(x_44);
lean_dec(x_17);
x_45 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__2;
x_46 = l_Lean_Name_append(x_1, x_45);
x_47 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_47, 0, x_1);
x_48 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__4;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__6;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_14);
x_53 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__8;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_10);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_10);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Std_PersistentArray_push___rarg(x_44, x_56);
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_43);
lean_ctor_set(x_16, 3, x_58);
x_59 = lean_st_ref_set(x_8, x_16, x_18);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_16, 0);
x_65 = lean_ctor_get(x_16, 1);
x_66 = lean_ctor_get(x_16, 2);
x_67 = lean_ctor_get(x_16, 4);
x_68 = lean_ctor_get(x_16, 5);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_16);
x_69 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
x_70 = lean_ctor_get(x_17, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_71 = x_17;
} else {
 lean_dec_ref(x_17);
 x_71 = lean_box(0);
}
x_72 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__2;
x_73 = l_Lean_Name_append(x_1, x_72);
x_74 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_74, 0, x_1);
x_75 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__4;
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__6;
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_14);
x_80 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__8;
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set(x_82, 1, x_81);
lean_inc(x_10);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_10);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Std_PersistentArray_push___rarg(x_70, x_83);
if (lean_is_scalar(x_71)) {
 x_85 = lean_alloc_ctor(0, 1, 1);
} else {
 x_85 = x_71;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_69);
x_86 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_86, 0, x_64);
lean_ctor_set(x_86, 1, x_65);
lean_ctor_set(x_86, 2, x_66);
lean_ctor_set(x_86, 3, x_85);
lean_ctor_set(x_86, 4, x_67);
lean_ctor_set(x_86, 5, x_68);
x_87 = lean_st_ref_set(x_8, x_86, x_18);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = lean_box(0);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 2);
x_10 = l_Lean_checkTraceOption(x_9, x_1);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_nat_dec_lt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_2, x_5);
if (x_9 == 0)
{
x_1 = x_7;
goto _start;
}
else
{
lean_object* x_11; 
lean_inc(x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_6);
return x_11;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = l_Std_RBNode_insert___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__1(x_17, x_1, x_2);
lean_ctor_set(x_14, 0, x_18);
x_19 = lean_st_ref_set(x_5, x_14, x_15);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = l_Std_RBNode_insert___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__1(x_26, x_1, x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_st_ref_set(x_5, x_29, x_15);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("annotate", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_52; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_4, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__2;
x_18 = lean_st_ref_get(x_8, x_14);
x_52 = l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__5(x_15, x_2);
lean_dec(x_15);
if (lean_obj_tag(x_52) == 0)
{
x_19 = x_16;
goto block_51;
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec(x_52);
x_19 = x_53;
goto block_51;
}
block_51:
{
uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_20 = 1;
lean_inc(x_1);
x_21 = l_Lean_KVMap_setBool(x_19, x_1, x_20);
x_41 = lean_ctor_get(x_18, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 3);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get_uint8(x_42, sizeof(void*)*1);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_dec(x_18);
x_45 = 0;
x_22 = x_45;
x_23 = x_44;
goto block_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_18, 1);
lean_inc(x_46);
lean_dec(x_18);
x_47 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__4(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_unbox(x_48);
lean_dec(x_48);
x_22 = x_50;
x_23 = x_49;
goto block_40;
}
block_40:
{
if (x_22 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___lambda__1(x_2, x_21, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_inc(x_2);
x_26 = l_Lean_SubExpr_Pos_toString(x_2);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__8;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__4;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_33, 0, x_1);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
x_36 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3(x_17, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___lambda__1(x_2, x_21, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_37);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_App_State_namedArgs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_7, x_6);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_5, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; 
lean_dec(x_9);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_5, x_22);
lean_dec(x_5);
x_32 = l_Lean_instInhabitedBinderInfo;
x_33 = lean_box(x_32);
x_34 = lean_array_get(x_33, x_3, x_6);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
x_36 = 0;
x_37 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_362_(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_11);
x_24 = x_39;
x_25 = x_18;
goto block_31;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_99; 
x_40 = l_Lean_instInhabitedExpr;
x_41 = lean_array_get(x_40, x_2, x_6);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_41);
x_99 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_typeUnknown(x_41, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_11);
x_42 = x_103;
x_43 = x_102;
goto block_98;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
lean_dec(x_99);
x_105 = lean_array_get(x_40, x_1, x_6);
lean_inc(x_4);
lean_inc(x_6);
x_106 = lean_apply_1(x_4, x_6);
x_107 = lean_unsigned_to_nat(10u);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_108 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp(x_105, x_106, x_107, x_12, x_13, x_14, x_15, x_16, x_17, x_104);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_11);
x_42 = x_111;
x_43 = x_110;
goto block_98;
}
else
{
uint8_t x_112; 
lean_dec(x_41);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
x_112 = !lean_is_exclusive(x_108);
if (x_112 == 0)
{
return x_108;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_108, 0);
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_108);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_41);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
x_116 = !lean_is_exclusive(x_99);
if (x_116 == 0)
{
return x_99;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_99, 0);
x_118 = lean_ctor_get(x_99, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_99);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
block_98:
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
uint8_t x_46; 
lean_dec(x_41);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_42, 0);
lean_dec(x_47);
x_48 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
lean_ctor_set(x_42, 0, x_48);
x_24 = x_42;
x_25 = x_43;
goto block_31;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_dec(x_42);
x_50 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_24 = x_51;
x_25 = x_43;
goto block_31;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_42, 1);
x_54 = lean_ctor_get(x_42, 0);
lean_dec(x_54);
x_55 = lean_array_get(x_40, x_1, x_6);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_56 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_55, x_41, x_12, x_13, x_14, x_15, x_16, x_17, x_43);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = !lean_is_exclusive(x_53);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_53, 0);
x_60 = 1;
x_61 = lean_box(x_60);
x_62 = lean_array_set(x_59, x_6, x_61);
lean_ctor_set(x_53, 0, x_62);
x_63 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
lean_ctor_set(x_42, 0, x_63);
x_24 = x_42;
x_25 = x_57;
goto block_31;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_64 = lean_ctor_get(x_53, 0);
x_65 = lean_ctor_get(x_53, 1);
x_66 = lean_ctor_get(x_53, 2);
x_67 = lean_ctor_get(x_53, 3);
x_68 = lean_ctor_get(x_53, 4);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_53);
x_69 = 1;
x_70 = lean_box(x_69);
x_71 = lean_array_set(x_64, x_6, x_70);
x_72 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_65);
lean_ctor_set(x_72, 2, x_66);
lean_ctor_set(x_72, 3, x_67);
lean_ctor_set(x_72, 4, x_68);
x_73 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
lean_ctor_set(x_42, 1, x_72);
lean_ctor_set(x_42, 0, x_73);
x_24 = x_42;
x_25 = x_57;
goto block_31;
}
}
else
{
uint8_t x_74; 
lean_free_object(x_42);
lean_dec(x_53);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
x_74 = !lean_is_exclusive(x_56);
if (x_74 == 0)
{
return x_56;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_56, 0);
x_76 = lean_ctor_get(x_56, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_56);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_42, 1);
lean_inc(x_78);
lean_dec(x_42);
x_79 = lean_array_get(x_40, x_1, x_6);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_80 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_79, x_41, x_12, x_13, x_14, x_15, x_16, x_17, x_43);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_ctor_get(x_78, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_78, 2);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_78, 4);
lean_inc(x_86);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 lean_ctor_release(x_78, 3);
 lean_ctor_release(x_78, 4);
 x_87 = x_78;
} else {
 lean_dec_ref(x_78);
 x_87 = lean_box(0);
}
x_88 = 1;
x_89 = lean_box(x_88);
x_90 = lean_array_set(x_82, x_6, x_89);
if (lean_is_scalar(x_87)) {
 x_91 = lean_alloc_ctor(0, 5, 0);
} else {
 x_91 = x_87;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_83);
lean_ctor_set(x_91, 2, x_84);
lean_ctor_set(x_91, 3, x_85);
lean_ctor_set(x_91, 4, x_86);
x_92 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_24 = x_93;
x_25 = x_81;
goto block_31;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_78);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
x_94 = lean_ctor_get(x_80, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_80, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_96 = x_80;
} else {
 lean_dec_ref(x_80);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
}
}
block_31:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_23;
x_6 = x_29;
x_9 = x_28;
x_11 = x_27;
x_18 = x_25;
goto _start;
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_9);
lean_ctor_set(x_120, 1, x_11);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_18);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_9);
lean_ctor_set(x_122, 1, x_11);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_18);
return x_123;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_array_get_size(x_1);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_19);
x_23 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___spec__1(x_1, x_2, x_3, x_17, x_19, x_20, x_19, x_21, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_4 = x_18;
x_5 = x_22;
x_7 = x_26;
x_14 = x_25;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instInhabitedExpr;
x_4 = lean_array_get(x_3, x_1, x_2);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lambda__2___boxed), 2, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___closed__1;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_box(0);
x_19 = l_List_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___spec__2(x_10, x_11, x_12, x_17, x_18, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_18);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
else
{
uint8_t x_32; 
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
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___spec__1___boxed(lean_object** _args) {
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
lean_object* x_19; 
x_19 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___lambda__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_6, x_5);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_4, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; 
lean_dec(x_8);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_4, x_21);
lean_dec(x_4);
x_23 = l_Lean_instInhabitedBinderInfo;
x_24 = lean_box(x_23);
x_25 = lean_array_get(x_24, x_3, x_5);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
x_27 = 3;
x_28 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_362_(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_30 = lean_box(0);
x_4 = x_22;
x_5 = x_29;
x_8 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = l_Lean_instInhabitedExpr;
x_33 = lean_array_get(x_32, x_1, x_5);
x_34 = lean_array_get(x_32, x_2, x_5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_35 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams(x_33, x_34, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_38 = lean_box(0);
x_4 = x_22;
x_5 = x_37;
x_8 = x_38;
x_17 = x_36;
goto _start;
}
else
{
uint8_t x_40; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
return x_35;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_35);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_8);
lean_ctor_set(x_44, 1, x_10);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_17);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_8);
lean_ctor_set(x_46, 1, x_10);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_17);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_array_get_size(x_10);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_box(0);
lean_inc(x_13);
x_17 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams___spec__1(x_10, x_11, x_12, x_13, x_14, x_13, x_15, x_16, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_13);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_16);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams___spec__1___boxed(lean_object** _args) {
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
x_18 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_1, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_6, 1);
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_array_set(x_18, x_3, x_20);
lean_ctor_set(x_6, 1, x_21);
x_22 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_ctor_get(x_6, 1);
x_26 = lean_ctor_get(x_6, 2);
x_27 = lean_ctor_get(x_6, 3);
x_28 = lean_ctor_get(x_6, 4);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_6);
x_29 = 1;
x_30 = lean_box(x_29);
x_31 = lean_array_set(x_25, x_3, x_30);
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_26);
lean_ctor_set(x_32, 3, x_27);
lean_ctor_set(x_32, 4, x_28);
x_33 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_14, 0, x_34);
return x_14;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_dec(x_14);
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_6, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_6, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_6, 4);
lean_inc(x_40);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_41 = x_6;
} else {
 lean_dec_ref(x_6);
 x_41 = lean_box(0);
}
x_42 = 1;
x_43 = lean_box(x_42);
x_44 = lean_array_set(x_37, x_3, x_43);
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(0, 5, 0);
} else {
 x_45 = x_41;
}
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_38);
lean_ctor_set(x_45, 3, x_39);
lean_ctor_set(x_45, 4, x_40);
x_46 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_35);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_6);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
return x_14;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_14, 0);
x_51 = lean_ctor_get(x_14, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_14);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_14 = lean_ctor_get(x_11, 2);
lean_inc(x_14);
x_15 = l_Lean_instInhabitedExpr;
x_16 = lean_array_get(x_15, x_1, x_2);
lean_dec(x_1);
lean_inc(x_16);
x_17 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(x_16, x_9, x_10, x_11, x_12, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_3);
x_20 = l_Lean_PrettyPrinter_Delaborator_isType2Type(x_3, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_PrettyPrinter_Delaborator_isFOLike(x_3, x_9, x_10, x_11, x_12, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = l_Lean_getPPAnalyzeTrustKnownFOType2TypeHOFuns(x_14);
lean_dec(x_14);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_free_object(x_23);
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_18);
x_28 = lean_box(0);
x_29 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__1(x_3, x_16, x_2, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
lean_dec(x_2);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_unbox(x_18);
lean_dec(x_18);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = lean_unbox(x_21);
lean_dec(x_21);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_free_object(x_23);
lean_dec(x_25);
x_32 = lean_box(0);
x_33 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__1(x_3, x_16, x_2, x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
lean_dec(x_2);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = lean_unbox(x_25);
lean_dec(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_free_object(x_23);
x_35 = lean_box(0);
x_36 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__1(x_3, x_16, x_2, x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
lean_dec(x_2);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_37 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_6);
lean_ctor_set(x_23, 0, x_38);
return x_23;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_free_object(x_23);
lean_dec(x_25);
lean_dec(x_21);
x_39 = lean_box(0);
x_40 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__1(x_3, x_16, x_2, x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
lean_dec(x_2);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_23, 0);
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_23);
x_43 = l_Lean_getPPAnalyzeTrustKnownFOType2TypeHOFuns(x_14);
lean_dec(x_14);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_41);
lean_dec(x_21);
lean_dec(x_18);
x_44 = lean_box(0);
x_45 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__1(x_3, x_16, x_2, x_44, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_42);
lean_dec(x_2);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = lean_unbox(x_18);
lean_dec(x_18);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = lean_unbox(x_21);
lean_dec(x_21);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_41);
x_48 = lean_box(0);
x_49 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__1(x_3, x_16, x_2, x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_42);
lean_dec(x_2);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = lean_unbox(x_41);
lean_dec(x_41);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_box(0);
x_52 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__1(x_3, x_16, x_2, x_51, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_42);
lean_dec(x_2);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_53 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_6);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_42);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_41);
lean_dec(x_21);
x_56 = lean_box(0);
x_57 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__1(x_3, x_16, x_2, x_56, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_42);
lean_dec(x_2);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_20);
if (x_58 == 0)
{
return x_20;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_20, 0);
x_60 = lean_ctor_get(x_20, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_20);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_4);
x_14 = lean_ctor_get(x_11, 2);
lean_inc(x_14);
x_15 = l_Lean_getPPAnalyzeTrustId(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__2(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = l_Lean_PrettyPrinter_Delaborator_isIdLike(x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__2(x_1, x_2, x_3, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_14 = l_Lean_instInhabitedExpr;
x_15 = lean_array_get(x_14, x_1, x_2);
lean_dec(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_15);
x_16 = lean_infer_type(x_15, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder___closed__1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_20 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_17, x_19, x_9, x_10, x_11, x_12, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_28 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_box(0);
x_33 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__3(x_3, x_2, x_15, x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_6, x_5);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_4, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; 
lean_dec(x_8);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_4, x_21);
lean_dec(x_4);
x_23 = l_Lean_instInhabitedBinderInfo;
x_24 = lean_box(x_23);
x_25 = lean_array_get(x_24, x_3, x_5);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
x_27 = 1;
x_28 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_362_(x_26, x_27);
if (x_28 == 0)
{
uint8_t x_29; uint8_t x_30; 
x_29 = 2;
x_30 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_362_(x_26, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_32 = lean_box(0);
x_4 = x_22;
x_5 = x_31;
x_8 = x_32;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_1);
x_35 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__4(x_1, x_5, x_2, x_34, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_35, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_36, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
lean_dec(x_37);
lean_ctor_set(x_36, 0, x_42);
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_35, 0, x_45);
return x_35;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_35, 1);
lean_inc(x_46);
lean_dec(x_35);
x_47 = lean_ctor_get(x_36, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_48 = x_36;
} else {
 lean_dec_ref(x_36);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_37, 0);
lean_inc(x_49);
lean_dec(x_37);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_46);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_35, 1);
lean_inc(x_52);
lean_dec(x_35);
x_53 = lean_ctor_get(x_36, 1);
lean_inc(x_53);
lean_dec(x_36);
x_54 = lean_ctor_get(x_37, 0);
lean_inc(x_54);
lean_dec(x_37);
x_55 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_22;
x_5 = x_55;
x_8 = x_54;
x_10 = x_53;
x_17 = x_52;
goto _start;
}
}
else
{
uint8_t x_57; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_35);
if (x_57 == 0)
{
return x_35;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_35, 0);
x_59 = lean_ctor_get(x_35, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_35);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_box(0);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_1);
x_62 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__4(x_1, x_5, x_2, x_61, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_62, 0);
lean_dec(x_66);
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_63, 0);
lean_dec(x_68);
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
lean_dec(x_64);
lean_ctor_set(x_63, 0, x_69);
return x_62;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_dec(x_63);
x_71 = lean_ctor_get(x_64, 0);
lean_inc(x_71);
lean_dec(x_64);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
lean_ctor_set(x_62, 0, x_72);
return x_62;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_62, 1);
lean_inc(x_73);
lean_dec(x_62);
x_74 = lean_ctor_get(x_63, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_75 = x_63;
} else {
 lean_dec_ref(x_63);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_64, 0);
lean_inc(x_76);
lean_dec(x_64);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_73);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_62, 1);
lean_inc(x_79);
lean_dec(x_62);
x_80 = lean_ctor_get(x_63, 1);
lean_inc(x_80);
lean_dec(x_63);
x_81 = lean_ctor_get(x_64, 0);
lean_inc(x_81);
lean_dec(x_64);
x_82 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_22;
x_5 = x_82;
x_8 = x_81;
x_10 = x_80;
x_17 = x_79;
goto _start;
}
}
else
{
uint8_t x_84; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_62);
if (x_84 == 0)
{
return x_62;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_62, 0);
x_86 = lean_ctor_get(x_62, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_62);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_8);
lean_ctor_set(x_88, 1, x_10);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_17);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_8);
lean_ctor_set(x_90, 1, x_10);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_17);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
x_13 = lean_array_get_size(x_10);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_box(0);
lean_inc(x_13);
x_17 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1(x_10, x_11, x_12, x_13, x_14, x_13, x_15, x_16, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
lean_dec(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_16);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1___boxed(lean_object** _args) {
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
x_18 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_1, 3);
x_11 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___spec__1___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp(x_16);
if (x_17 == 0)
{
lean_object* x_65; 
x_65 = lean_box(x_17);
lean_ctor_set(x_12, 0, x_65);
x_18 = x_12;
x_19 = x_13;
goto block_64;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = l_Lean_instInhabitedExpr;
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_array_get(x_66, x_10, x_67);
x_69 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(x_68, x_5, x_6, x_7, x_8, x_13);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_unbox(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_70);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_array_get(x_66, x_10, x_73);
x_75 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(x_74, x_5, x_6, x_7, x_8, x_72);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_ctor_set(x_12, 0, x_76);
x_18 = x_12;
x_19 = x_77;
goto block_64;
}
else
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_69, 1);
lean_inc(x_78);
lean_dec(x_69);
lean_ctor_set(x_12, 0, x_70);
x_18 = x_12;
x_19 = x_78;
goto block_64;
}
}
block_64:
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_18, 0, x_24);
if (lean_is_scalar(x_14)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_14;
}
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
if (lean_is_scalar(x_14)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_14;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_19);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_14);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_18, 1);
x_32 = lean_ctor_get(x_18, 0);
lean_dec(x_32);
x_33 = l_Lean_instInhabitedExpr;
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_array_get(x_33, x_10, x_34);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_array_get(x_33, x_10, x_36);
x_38 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_35, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_ctor_set(x_18, 0, x_40);
lean_ctor_set(x_38, 0, x_18);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_38, 0);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_38);
lean_ctor_set(x_18, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_18);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_free_object(x_18);
lean_dec(x_31);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_18, 1);
lean_inc(x_48);
lean_dec(x_18);
x_49 = l_Lean_instInhabitedExpr;
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_array_get(x_49, x_10, x_50);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_array_get(x_49, x_10, x_52);
x_54 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_51, x_53, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_48);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_48);
x_60 = lean_ctor_get(x_54, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_62 = x_54;
} else {
 lean_dec_ref(x_54);
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
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_12, 0);
x_80 = lean_ctor_get(x_12, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_12);
x_81 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp(x_79);
if (x_81 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_box(x_81);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_80);
x_82 = x_110;
x_83 = x_13;
goto block_108;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_111 = l_Lean_instInhabitedExpr;
x_112 = lean_unsigned_to_nat(0u);
x_113 = lean_array_get(x_111, x_10, x_112);
x_114 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(x_113, x_5, x_6, x_7, x_8, x_13);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_unbox(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_115);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_array_get(x_111, x_10, x_118);
x_120 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(x_119, x_5, x_6, x_7, x_8, x_117);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_80);
x_82 = x_123;
x_83 = x_122;
goto block_108;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_114, 1);
lean_inc(x_124);
lean_dec(x_114);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_115);
lean_ctor_set(x_125, 1, x_80);
x_82 = x_125;
x_83 = x_124;
goto block_108;
}
}
block_108:
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_87 = x_82;
} else {
 lean_dec_ref(x_82);
 x_87 = lean_box(0);
}
x_88 = lean_box(0);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
if (lean_is_scalar(x_14)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_14;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_83);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_14);
x_91 = lean_ctor_get(x_82, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_92 = x_82;
} else {
 lean_dec_ref(x_82);
 x_92 = lean_box(0);
}
x_93 = l_Lean_instInhabitedExpr;
x_94 = lean_unsigned_to_nat(0u);
x_95 = lean_array_get(x_93, x_10, x_94);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_array_get(x_93, x_10, x_96);
x_98 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_95, x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_83);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_92;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_91);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_92);
lean_dec(x_91);
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_106 = x_98;
} else {
 lean_dec_ref(x_98);
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
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_6, x_5);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_4, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; 
lean_dec(x_8);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_4, x_21);
lean_dec(x_4);
x_31 = l_Lean_instInhabitedBinderInfo;
x_32 = lean_box(x_31);
x_33 = lean_array_get(x_32, x_3, x_5);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
x_35 = 0;
x_36 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_362_(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_10);
x_23 = x_38;
x_24 = x_17;
goto block_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_39 = l_Lean_instInhabitedExpr;
x_40 = lean_array_get(x_39, x_2, x_5);
lean_inc(x_40);
x_98 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(x_40, x_13, x_14, x_15, x_16, x_17);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_unbox(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_10);
x_41 = x_102;
x_42 = x_101;
goto block_97;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_99);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_dec(x_98);
x_104 = lean_array_get(x_39, x_1, x_5);
x_105 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp(x_104, x_11, x_12, x_13, x_14, x_15, x_16, x_103);
lean_dec(x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_10);
x_41 = x_108;
x_42 = x_107;
goto block_97;
}
block_97:
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
lean_dec(x_40);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
lean_ctor_set(x_41, 0, x_47);
x_23 = x_41;
x_24 = x_42;
goto block_30;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_23 = x_50;
x_24 = x_42;
goto block_30;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_41);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_41, 1);
x_53 = lean_ctor_get(x_41, 0);
lean_dec(x_53);
x_54 = lean_array_get(x_39, x_1, x_5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_55 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_54, x_40, x_11, x_12, x_13, x_14, x_15, x_16, x_42);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = 1;
x_60 = lean_box(x_59);
x_61 = lean_array_set(x_58, x_5, x_60);
lean_ctor_set(x_52, 0, x_61);
x_62 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
lean_ctor_set(x_41, 0, x_62);
x_23 = x_41;
x_24 = x_56;
goto block_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_52, 0);
x_64 = lean_ctor_get(x_52, 1);
x_65 = lean_ctor_get(x_52, 2);
x_66 = lean_ctor_get(x_52, 3);
x_67 = lean_ctor_get(x_52, 4);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_52);
x_68 = 1;
x_69 = lean_box(x_68);
x_70 = lean_array_set(x_63, x_5, x_69);
x_71 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_64);
lean_ctor_set(x_71, 2, x_65);
lean_ctor_set(x_71, 3, x_66);
lean_ctor_set(x_71, 4, x_67);
x_72 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
lean_ctor_set(x_41, 1, x_71);
lean_ctor_set(x_41, 0, x_72);
x_23 = x_41;
x_24 = x_56;
goto block_30;
}
}
else
{
uint8_t x_73; 
lean_free_object(x_41);
lean_dec(x_52);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
x_73 = !lean_is_exclusive(x_55);
if (x_73 == 0)
{
return x_55;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_55, 0);
x_75 = lean_ctor_get(x_55, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_55);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_41, 1);
lean_inc(x_77);
lean_dec(x_41);
x_78 = lean_array_get(x_39, x_1, x_5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_79 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_78, x_40, x_11, x_12, x_13, x_14, x_15, x_16, x_42);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_ctor_get(x_77, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_77, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_77, 4);
lean_inc(x_85);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 x_86 = x_77;
} else {
 lean_dec_ref(x_77);
 x_86 = lean_box(0);
}
x_87 = 1;
x_88 = lean_box(x_87);
x_89 = lean_array_set(x_81, x_5, x_88);
if (lean_is_scalar(x_86)) {
 x_90 = lean_alloc_ctor(0, 5, 0);
} else {
 x_90 = x_86;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_82);
lean_ctor_set(x_90, 2, x_83);
lean_ctor_set(x_90, 3, x_84);
lean_ctor_set(x_90, 4, x_85);
x_91 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_23 = x_92;
x_24 = x_80;
goto block_30;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_77);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
x_93 = lean_ctor_get(x_79, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_79, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_95 = x_79;
} else {
 lean_dec_ref(x_79);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
}
block_30:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_22;
x_5 = x_28;
x_8 = x_27;
x_10 = x_26;
x_17 = x_24;
goto _start;
}
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_8);
lean_ctor_set(x_109, 1, x_10);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_17);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_8);
lean_ctor_set(x_111, 1, x_10);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_17);
return x_112;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_array_get_size(x_10);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_box(0);
lean_inc(x_13);
x_17 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps___spec__1(x_10, x_11, x_12, x_13, x_14, x_13, x_15, x_16, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_13);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_16);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps___spec__1___boxed(lean_object** _args) {
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
x_18 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_4(x_1, x_2, x_3, x_4, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_12;
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
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
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
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_23 = x_19;
} else {
 lean_dec_ref(x_19);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__1___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
x_13 = l_Lean_Meta_checkpointDefEq___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq___spec__1(x_1, x_2, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_4);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("funBinderTypes", 14);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__2;
x_2 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_7, x_6);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_5, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_41; lean_object* x_42; uint8_t x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_5, x_22);
lean_dec(x_5);
x_85 = l_Lean_instInhabitedBinderInfo;
x_86 = lean_box(x_85);
x_87 = lean_array_get(x_86, x_3, x_6);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
x_89 = 1;
x_90 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_362_(x_88, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_box(x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_11);
x_41 = x_92;
x_42 = x_18;
goto block_84;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_93 = l_Lean_instInhabitedExpr;
x_94 = lean_array_get(x_93, x_2, x_6);
lean_inc(x_94);
x_95 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(x_94, x_14, x_15, x_16, x_17, x_18);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_unbox(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_94);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_11);
x_41 = x_99;
x_42 = x_98;
goto block_84;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_96);
x_100 = lean_ctor_get(x_95, 1);
lean_inc(x_100);
lean_dec(x_95);
lean_inc(x_4);
x_101 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___lambda__1___boxed), 11, 2);
lean_closure_set(x_101, 0, x_4);
lean_closure_set(x_101, 1, x_94);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
x_102 = l_Lean_Meta_withNewMCtxDepth___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__1___rarg(x_101, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_100);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_41 = x_103;
x_42 = x_104;
goto block_84;
}
else
{
uint8_t x_105; 
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
x_105 = !lean_is_exclusive(x_102);
if (x_105 == 0)
{
return x_102;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_102, 0);
x_107 = lean_ctor_get(x_102, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_102);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
block_40:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_ctor_get(x_26, 0);
lean_inc(x_36);
lean_dec(x_26);
x_37 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_38 = lean_unbox(x_36);
lean_dec(x_36);
x_5 = x_23;
x_6 = x_37;
x_9 = x_38;
x_11 = x_35;
x_18 = x_25;
goto _start;
}
}
block_84:
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = lean_box(x_9);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_41, 0, x_48);
x_24 = x_41;
x_25 = x_42;
goto block_40;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_dec(x_41);
x_50 = lean_box(x_9);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
x_24 = x_52;
x_25 = x_42;
goto block_40;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_41);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_41, 1);
x_55 = lean_ctor_get(x_41, 0);
lean_dec(x_55);
x_56 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__2;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_57 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_56, x_12, x_13, x_14, x_15, x_16, x_17, x_42);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_instInhabitedExpr;
x_60 = lean_array_get(x_59, x_1, x_6);
x_61 = lean_array_get(x_59, x_2, x_6);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_62 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_60, x_61, x_12, x_13, x_14, x_15, x_16, x_17, x_58);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__3;
lean_ctor_set(x_41, 0, x_64);
x_24 = x_41;
x_25 = x_63;
goto block_40;
}
else
{
uint8_t x_65; 
lean_free_object(x_41);
lean_dec(x_54);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
return x_62;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_62, 0);
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_62);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_41, 1);
lean_inc(x_69);
lean_dec(x_41);
x_70 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__2;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_71 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_70, x_12, x_13, x_14, x_15, x_16, x_17, x_42);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l_Lean_instInhabitedExpr;
x_74 = lean_array_get(x_73, x_1, x_6);
x_75 = lean_array_get(x_73, x_2, x_6);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_76 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_74, x_75, x_12, x_13, x_14, x_15, x_16, x_17, x_72);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__3;
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_69);
x_24 = x_79;
x_25 = x_77;
goto block_40;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_69);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
x_80 = lean_ctor_get(x_76, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_82 = x_76;
} else {
 lean_dec_ref(x_76);
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
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_109 = lean_box(x_9);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_11);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_18);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_112 = lean_box(x_9);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_11);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_18);
return x_114;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_SubExpr_Pos_push(x_15, x_2);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_6, 0, x_17);
x_18 = lean_apply_9(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
else
{
uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_20 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
x_21 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 2);
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_23);
lean_dec(x_6);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_SubExpr_Pos_push(x_24, x_2);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_19);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 1, x_20);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 2, x_21);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 3, x_22);
x_28 = lean_apply_9(x_3, x_4, x_5, x_27, x_7, x_8, x_9, x_10, x_11, x_12);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__5___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_10(x_1, x_6, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__5___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__5___rarg___lambda__1), 11, 5);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_5);
lean_closure_set(x_14, 2, x_6);
lean_closure_set(x_14, 3, x_7);
lean_closure_set(x_14, 4, x_8);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_14, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_26 = x_22;
} else {
 lean_dec_ref(x_22);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__5___rarg___boxed), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_Expr_bindingBody_x21(x_1);
lean_dec(x_1);
x_14 = lean_expr_instantiate1(x_13, x_3);
lean_dec(x_3);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__4(x_14, x_15, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___spec__1___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_17 = l_Lean_Expr_binderInfo(x_15);
x_18 = l_Lean_Expr_bindingDomain_x21(x_15);
x_19 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__3___lambda__1), 12, 2);
lean_closure_set(x_19, 0, x_15);
lean_closure_set(x_19, 1, x_2);
x_20 = l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__5___rarg(x_1, x_17, x_18, x_19, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___spec__1___rarg(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 6)
{
lean_dec(x_17);
if (lean_obj_tag(x_5) == 7)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_5, 2);
lean_inc(x_21);
lean_dec(x_5);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_unsigned_to_nat(1u);
x_24 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_4);
x_25 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2(x_1, x_2, x_3, x_20, x_4, x_22, x_4, x_23, x_24, x_6, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_18);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core), 14, 5);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_2);
lean_closure_set(x_30, 2, x_3);
lean_closure_set(x_30, 3, x_4);
lean_closure_set(x_30, 4, x_21);
x_31 = lean_box(0);
x_32 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__3(x_31, x_30, x_6, x_29, x_8, x_9, x_10, x_11, x_12, x_13, x_27);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_28);
lean_dec(x_28);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_32, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_32, 0, x_40);
return x_32;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_44 = x_33;
} else {
 lean_dec_ref(x_33);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_32);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_32, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_33);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_33, 0);
lean_dec(x_50);
x_51 = 1;
x_52 = lean_box(x_51);
lean_ctor_set(x_33, 0, x_52);
return x_32;
}
else
{
lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_33, 1);
lean_inc(x_53);
lean_dec(x_33);
x_54 = 1;
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_32, 0, x_56);
return x_32;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_32, 1);
lean_inc(x_57);
lean_dec(x_32);
x_58 = lean_ctor_get(x_33, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_59 = x_33;
} else {
 lean_dec_ref(x_33);
 x_59 = lean_box(0);
}
x_60 = 1;
x_61 = lean_box(x_60);
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_59;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_58);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_57);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_28);
x_64 = !lean_is_exclusive(x_32);
if (x_64 == 0)
{
return x_32;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_32, 0);
x_66 = lean_ctor_get(x_32, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_32);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_25);
if (x_68 == 0)
{
return x_25;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_25, 0);
x_70 = lean_ctor_get(x_25, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_25);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_15);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_15, 0);
lean_dec(x_73);
x_74 = !lean_is_exclusive(x_16);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_16, 0);
lean_dec(x_75);
x_76 = 0;
x_77 = lean_box(x_76);
lean_ctor_set(x_16, 0, x_77);
return x_15;
}
else
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_16, 1);
lean_inc(x_78);
lean_dec(x_16);
x_79 = 0;
x_80 = lean_box(x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
lean_ctor_set(x_15, 0, x_81);
return x_15;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_82 = lean_ctor_get(x_15, 1);
lean_inc(x_82);
lean_dec(x_15);
x_83 = lean_ctor_get(x_16, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_84 = x_16;
} else {
 lean_dec_ref(x_16);
 x_84 = lean_box(0);
}
x_85 = 0;
x_86 = lean_box(x_85);
if (lean_is_scalar(x_84)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_84;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_83);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_82);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_15);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_15, 0);
lean_dec(x_90);
x_91 = !lean_is_exclusive(x_16);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_16, 0);
lean_dec(x_92);
x_93 = 0;
x_94 = lean_box(x_93);
lean_ctor_set(x_16, 0, x_94);
return x_15;
}
else
{
lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_16, 1);
lean_inc(x_95);
lean_dec(x_16);
x_96 = 0;
x_97 = lean_box(x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set(x_15, 0, x_98);
return x_15;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_15, 1);
lean_inc(x_99);
lean_dec(x_15);
x_100 = lean_ctor_get(x_16, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_101 = x_16;
} else {
 lean_dec_ref(x_16);
 x_101 = lean_box(0);
}
x_102 = 0;
x_103 = lean_box(x_102);
if (lean_is_scalar(x_101)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_101;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_100);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_99);
return x_105;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___boxed(lean_object** _args) {
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
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_9);
lean_dec(x_9);
x_20 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__5___rarg(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__2___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___spec__1___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Expr_getAppNumArgsAux(x_15, x_17);
x_19 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams___closed__1;
lean_inc(x_18);
x_20 = lean_mk_array(x_18, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_18, x_21);
lean_dec(x_18);
x_23 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_15, x_20, x_22);
x_24 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__2___rarg(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_array_get_size(x_23);
x_30 = l_Lean_SubExpr_Pos_pushNaryArg(x_29, x_1, x_27);
lean_dec(x_27);
lean_dec(x_29);
x_31 = !lean_is_exclusive(x_5);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_5, 0);
lean_dec(x_32);
x_33 = l_Lean_instInhabitedExpr;
x_34 = lean_array_get(x_33, x_23, x_1);
lean_dec(x_23);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_5, 0, x_35);
x_36 = lean_apply_9(x_2, x_3, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
return x_36;
}
else
{
uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_38 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_39 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_40 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
lean_dec(x_5);
x_41 = l_Lean_instInhabitedExpr;
x_42 = lean_array_get(x_41, x_23, x_1);
lean_dec(x_23);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_30);
x_44 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_37);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 1, x_38);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 2, x_39);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 3, x_40);
x_45 = lean_apply_9(x_2, x_3, x_28, x_44, x_6, x_7, x_8, x_9, x_10, x_26);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_6, x_5);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_4, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; 
lean_dec(x_8);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_4, x_21);
lean_dec(x_4);
x_31 = l_Lean_instInhabitedBinderInfo;
x_32 = lean_box(x_31);
x_33 = lean_array_get(x_32, x_3, x_5);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
x_35 = 0;
x_36 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_362_(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_10);
x_23 = x_38;
x_24 = x_17;
goto block_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = l_Lean_instInhabitedExpr;
x_40 = lean_array_get(x_39, x_2, x_5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_41 = lean_infer_type(x_40, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_44 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core), 14, 5);
lean_closure_set(x_44, 0, x_1);
lean_closure_set(x_44, 1, x_2);
lean_closure_set(x_44, 2, x_3);
lean_closure_set(x_44, 3, x_5);
lean_closure_set(x_44, 4, x_42);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_45 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__1(x_5, x_44, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_46, 0);
lean_dec(x_51);
x_52 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
lean_ctor_set(x_46, 0, x_52);
x_23 = x_46;
x_24 = x_49;
goto block_30;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_23 = x_55;
x_24 = x_49;
goto block_30;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_46);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_46, 1);
x_58 = lean_ctor_get(x_46, 0);
lean_dec(x_58);
x_59 = lean_ctor_get(x_45, 1);
lean_inc(x_59);
lean_dec(x_45);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_57, 2);
x_62 = 1;
x_63 = lean_box(x_62);
x_64 = lean_array_set(x_61, x_5, x_63);
lean_ctor_set(x_57, 2, x_64);
x_65 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
lean_ctor_set(x_46, 0, x_65);
x_23 = x_46;
x_24 = x_59;
goto block_30;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_66 = lean_ctor_get(x_57, 0);
x_67 = lean_ctor_get(x_57, 1);
x_68 = lean_ctor_get(x_57, 2);
x_69 = lean_ctor_get(x_57, 3);
x_70 = lean_ctor_get(x_57, 4);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_57);
x_71 = 1;
x_72 = lean_box(x_71);
x_73 = lean_array_set(x_68, x_5, x_72);
x_74 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_74, 0, x_66);
lean_ctor_set(x_74, 1, x_67);
lean_ctor_set(x_74, 2, x_73);
lean_ctor_set(x_74, 3, x_69);
lean_ctor_set(x_74, 4, x_70);
x_75 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
lean_ctor_set(x_46, 1, x_74);
lean_ctor_set(x_46, 0, x_75);
x_23 = x_46;
x_24 = x_59;
goto block_30;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_76 = lean_ctor_get(x_46, 1);
lean_inc(x_76);
lean_dec(x_46);
x_77 = lean_ctor_get(x_45, 1);
lean_inc(x_77);
lean_dec(x_45);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_76, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_76, 3);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 4);
lean_inc(x_82);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 lean_ctor_release(x_76, 2);
 lean_ctor_release(x_76, 3);
 lean_ctor_release(x_76, 4);
 x_83 = x_76;
} else {
 lean_dec_ref(x_76);
 x_83 = lean_box(0);
}
x_84 = 1;
x_85 = lean_box(x_84);
x_86 = lean_array_set(x_80, x_5, x_85);
if (lean_is_scalar(x_83)) {
 x_87 = lean_alloc_ctor(0, 5, 0);
} else {
 x_87 = x_83;
}
lean_ctor_set(x_87, 0, x_78);
lean_ctor_set(x_87, 1, x_79);
lean_ctor_set(x_87, 2, x_86);
lean_ctor_set(x_87, 3, x_81);
lean_ctor_set(x_87, 4, x_82);
x_88 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_23 = x_89;
x_24 = x_77;
goto block_30;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_45);
if (x_90 == 0)
{
return x_45;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_45, 0);
x_92 = lean_ctor_get(x_45, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_45);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_41);
if (x_94 == 0)
{
return x_41;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_41, 0);
x_96 = lean_ctor_get(x_41, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_41);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
block_30:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_22;
x_5 = x_28;
x_8 = x_27;
x_10 = x_26;
x_17 = x_24;
goto _start;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_8);
lean_ctor_set(x_98, 1, x_10);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_17);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_8);
lean_ctor_set(x_100, 1, x_10);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_17);
return x_101;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
x_13 = lean_array_get_size(x_10);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_box(0);
lean_inc(x_13);
x_17 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__3(x_10, x_11, x_12, x_13, x_14, x_13, x_15, x_16, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_13);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_16);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__3___boxed(lean_object** _args) {
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
x_18 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_7);
lean_dec(x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_infer_type(x_10, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Expr_isForall(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; 
x_18 = l_Lean_Expr_bindingInfo_x21(x_14);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
x_20 = 1;
x_21 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_362_(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(0);
lean_ctor_set(x_12, 0, x_22);
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_12);
x_23 = l_Lean_getPPAnalysisBlockImplicit___closed__2;
x_24 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_23, x_1, x_2, x_3, x_4, x_5, x_6, x_15);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = l_Lean_Expr_isForall(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; 
x_30 = l_Lean_Expr_bindingInfo_x21(x_25);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
x_32 = 1;
x_33 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_362_(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Lean_getPPAnalysisBlockImplicit___closed__2;
x_37 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_36, x_1, x_2, x_3, x_4, x_5, x_6, x_26);
return x_37;
}
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
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
return x_12;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_12, 0);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_12);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_7);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeSort___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeSort(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeSort___rarg), 1, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeSort___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeSort(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1___closed__1;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1___closed__2;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1___closed__3;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__2(x_1, x_4);
x_6 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_containsBadMax(x_3);
if (x_6 == 0)
{
return x_5;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.PrettyPrinter.Delaborator.TopDownAnalyze", 45);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.PrettyPrinter.Delaborator.TopDownAnalyze.analyze.analyzeConst", 66);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__1;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__2;
x_3 = lean_unsigned_to_nat(444u);
x_4 = lean_unsigned_to_nat(41u);
x_5 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___lambda__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("universes", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__2;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 4)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__5;
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_List_isEmpty___rarg(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_5, 2);
lean_inc(x_15);
x_16 = l_Lean_getPPAnalyzeOmitMax(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
x_17 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__7;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_17, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_apply_8(x_12, x_19, x_1, x_2, x_3, x_4, x_5, x_6, x_20);
return x_21;
}
else
{
uint8_t x_22; uint8_t x_23; 
x_22 = 0;
x_23 = l_List_foldr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__2(x_22, x_11);
lean_dec(x_11);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__7;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_25 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_24, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_apply_8(x_12, x_26, x_1, x_2, x_3, x_4, x_5, x_6, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(0);
x_30 = lean_apply_8(x_12, x_29, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_11);
x_31 = lean_box(0);
x_32 = lean_apply_8(x_12, x_31, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_11);
x_33 = lean_box(0);
x_34 = lean_apply_8(x_12, x_33, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_dec(x_8);
x_36 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__4;
x_37 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1(x_36, x_1, x_2, x_3, x_4, x_5, x_6, x_35);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__2(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_getPPAnalysisNamedArg___closed__2;
x_12 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_3, 4);
x_17 = lean_array_push(x_16, x_1);
lean_ctor_set(x_3, 4, x_17);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
x_22 = lean_ctor_get(x_3, 2);
x_23 = lean_ctor_get(x_3, 3);
x_24 = lean_ctor_get(x_3, 4);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
x_25 = lean_array_push(x_24, x_1);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_23);
lean_ctor_set(x_26, 4, x_25);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_12, 0, x_28);
return x_12;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_dec(x_12);
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_3, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_3, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 4);
lean_inc(x_34);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_35 = x_3;
} else {
 lean_dec_ref(x_3);
 x_35 = lean_box(0);
}
x_36 = lean_array_push(x_34, x_1);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 5, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_31);
lean_ctor_set(x_37, 2, x_32);
lean_ctor_set(x_37, 3, x_33);
lean_ctor_set(x_37, 4, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_29);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasMVar(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_st_ref_get(x_9, x_10);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_7, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_instantiateMVarsCore(x_19, x_1);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_20, 1);
x_23 = lean_st_ref_get(x_9, x_18);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_take(x_7, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
lean_ctor_set(x_26, 0, x_22);
x_30 = lean_st_ref_set(x_7, x_26, x_27);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_30, 0, x_20);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
lean_ctor_set(x_20, 1, x_3);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_20);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_26, 1);
x_36 = lean_ctor_get(x_26, 2);
x_37 = lean_ctor_get(x_26, 3);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_22);
lean_ctor_set(x_38, 1, x_35);
lean_ctor_set(x_38, 2, x_36);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_st_ref_set(x_7, x_38, x_27);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
lean_ctor_set(x_20, 1, x_3);
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_20);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_43 = lean_ctor_get(x_20, 0);
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_20);
x_45 = lean_st_ref_get(x_9, x_18);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_st_ref_take(x_7, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 3);
lean_inc(x_52);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 x_53 = x_48;
} else {
 lean_dec_ref(x_48);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 4, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set(x_54, 3, x_52);
x_55 = lean_st_ref_set(x_7, x_54, x_49);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_43);
lean_ctor_set(x_58, 1, x_3);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Expr_getAppNumArgsAux(x_10, x_15);
x_17 = l_Lean_SubExpr_Pos_pushNaryFn(x_16, x_13);
lean_dec(x_13);
lean_dec(x_16);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_2, 0);
lean_dec(x_19);
x_20 = l_Lean_Expr_getAppFn(x_10);
lean_dec(x_10);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_2, 0, x_21);
x_22 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
return x_22;
}
else
{
uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_24 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_25 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 2);
x_26 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 3);
lean_dec(x_2);
x_27 = l_Lean_Expr_getAppFn(x_10);
lean_dec(x_10);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_17);
x_29 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_23);
lean_ctor_set_uint8(x_29, sizeof(void*)*1 + 1, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*1 + 2, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*1 + 3, x_26);
x_30 = lean_apply_7(x_1, x_29, x_3, x_4, x_5, x_6, x_7, x_14);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_13 = l_Lean_Expr_isApp(x_10);
lean_dec(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = l_Lean_instantiateMVars___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn___spec__1(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth(x_18, x_5, x_6, x_7, x_8, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn___spec__2), 8, 1);
lean_closure_set(x_26, 0, x_25);
if (x_12 == 0)
{
uint8_t x_27; 
x_27 = lean_unbox(x_21);
lean_dec(x_21);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; 
x_28 = 0;
x_29 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg(x_28, x_23, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_ctor_set(x_15, 0, x_31);
lean_ctor_set(x_29, 0, x_15);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_29);
lean_ctor_set(x_15, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_15);
lean_dec(x_19);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; lean_object* x_40; 
x_39 = 0;
x_40 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg(x_39, x_39, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_ctor_set(x_15, 0, x_42);
lean_ctor_set(x_40, 0, x_15);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_40);
lean_ctor_set(x_15, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_free_object(x_15);
lean_dec(x_19);
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
return x_40;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_40, 0);
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_40);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_50; lean_object* x_51; 
lean_dec(x_21);
x_50 = 0;
x_51 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg(x_50, x_23, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_ctor_set(x_15, 0, x_53);
lean_ctor_set(x_51, 0, x_15);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_51);
lean_ctor_set(x_15, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_15);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_free_object(x_15);
lean_dec(x_19);
x_57 = !lean_is_exclusive(x_51);
if (x_57 == 0)
{
return x_51;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_51, 0);
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_51);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = lean_ctor_get(x_15, 0);
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_15);
x_63 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_hasLevelMVarAtCurrDepth(x_61, x_5, x_6, x_7, x_8, x_16);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = 1;
x_67 = lean_box(x_66);
x_68 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_68, 0, x_67);
x_69 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn___spec__2), 8, 1);
lean_closure_set(x_69, 0, x_68);
if (x_12 == 0)
{
uint8_t x_70; 
x_70 = lean_unbox(x_64);
lean_dec(x_64);
if (x_70 == 0)
{
uint8_t x_71; lean_object* x_72; 
x_71 = 0;
x_72 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg(x_71, x_66, x_69, x_3, x_4, x_5, x_6, x_7, x_8, x_65);
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
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_62);
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
lean_dec(x_62);
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
uint8_t x_82; lean_object* x_83; 
x_82 = 0;
x_83 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg(x_82, x_82, x_69, x_3, x_4, x_5, x_6, x_7, x_8, x_65);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_62);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_62);
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_91 = x_83;
} else {
 lean_dec_ref(x_83);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
uint8_t x_93; lean_object* x_94; 
lean_dec(x_64);
x_93 = 0;
x_94 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg(x_93, x_66, x_69, x_3, x_4, x_5, x_6, x_7, x_8, x_65);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_62);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_62);
x_100 = lean_ctor_get(x_94, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_94, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_102 = x_94;
} else {
 lean_dec_ref(x_94);
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
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_2);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_9);
return x_106;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_SubExpr_Pos_push(x_13, x_2);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_4, 0, x_15);
x_16 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
else
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_18 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 2);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 3);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_SubExpr_Pos_push(x_22, x_2);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_17);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 1, x_18);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 2, x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 3, x_20);
x_26 = lean_apply_7(x_3, x_25, x_5, x_6, x_7, x_8, x_9, x_10);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = lean_infer_type(x_10, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_SubExpr_Pos_typeCoord;
x_16 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___spec__2(x_13, x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
lean_dec(x_2);
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_7, 2);
lean_inc(x_14);
x_15 = l_Lean_Expr_isAtomic(x_11);
if (x_15 == 0)
{
uint8_t x_92; 
x_92 = l_Lean_getPPProofs(x_14);
if (x_92 == 0)
{
lean_object* x_93; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_93 = l_Lean_Meta_isProof(x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_unbox(x_94);
lean_dec(x_94);
x_16 = x_96;
x_17 = x_95;
goto block_91;
}
else
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_dec(x_93);
x_98 = 0;
x_16 = x_98;
x_17 = x_97;
goto block_91;
}
}
else
{
uint8_t x_99; 
lean_dec(x_11);
x_99 = 0;
x_16 = x_99;
x_17 = x_12;
goto block_91;
}
}
else
{
uint8_t x_100; 
lean_dec(x_11);
x_100 = 0;
x_16 = x_100;
x_17 = x_12;
goto block_91;
}
block_91:
{
if (x_16 == 0)
{
uint8_t x_18; 
lean_dec(x_14);
lean_dec(x_13);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 3, x_1);
x_19 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
switch (lean_obj_tag(x_20)) {
case 1:
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit(x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_22;
}
case 4:
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst(x_3, x_4, x_5, x_6, x_7, x_8, x_23);
return x_24;
}
case 5:
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp(x_3, x_4, x_5, x_6, x_7, x_8, x_25);
return x_26;
}
case 6:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_20);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam(x_3, x_4, x_5, x_6, x_7, x_8, x_27);
return x_28;
}
case 7:
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_20);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzePi(x_3, x_4, x_5, x_6, x_7, x_8, x_29);
return x_30;
}
case 8:
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_20);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_dec(x_19);
x_32 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet(x_3, x_4, x_5, x_6, x_7, x_8, x_31);
return x_32;
}
case 10:
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_20);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_dec(x_19);
x_34 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData(x_3, x_4, x_5, x_6, x_7, x_8, x_33);
return x_34;
}
case 11:
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_20);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_dec(x_19);
x_36 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj(x_3, x_4, x_5, x_6, x_7, x_8, x_35);
return x_36;
}
default: 
{
uint8_t x_37; 
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_19);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_19, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_19, 0, x_39);
return x_19;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_dec(x_19);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
}
else
{
uint8_t x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_44 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_45 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
lean_dec(x_3);
x_47 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_43);
lean_ctor_set_uint8(x_47, sizeof(void*)*1 + 1, x_44);
lean_ctor_set_uint8(x_47, sizeof(void*)*1 + 2, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1 + 3, x_1);
x_48 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_47, x_4, x_5, x_6, x_7, x_8, x_17);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
switch (lean_obj_tag(x_49)) {
case 1:
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit(x_47, x_4, x_5, x_6, x_7, x_8, x_50);
return x_51;
}
case 4:
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_49);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst(x_47, x_4, x_5, x_6, x_7, x_8, x_52);
return x_53;
}
case 5:
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_49);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_dec(x_48);
x_55 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp(x_47, x_4, x_5, x_6, x_7, x_8, x_54);
return x_55;
}
case 6:
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_49);
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
lean_dec(x_48);
x_57 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam(x_47, x_4, x_5, x_6, x_7, x_8, x_56);
return x_57;
}
case 7:
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_49);
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_dec(x_48);
x_59 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzePi(x_47, x_4, x_5, x_6, x_7, x_8, x_58);
return x_59;
}
case 8:
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_49);
x_60 = lean_ctor_get(x_48, 1);
lean_inc(x_60);
lean_dec(x_48);
x_61 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet(x_47, x_4, x_5, x_6, x_7, x_8, x_60);
return x_61;
}
case 10:
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_49);
x_62 = lean_ctor_get(x_48, 1);
lean_inc(x_62);
lean_dec(x_48);
x_63 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData(x_47, x_4, x_5, x_6, x_7, x_8, x_62);
return x_63;
}
case 11:
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_49);
x_64 = lean_ctor_get(x_48, 1);
lean_inc(x_64);
lean_dec(x_48);
x_65 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj(x_47, x_4, x_5, x_6, x_7, x_8, x_64);
return x_65;
}
default: 
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_66 = lean_ctor_get(x_48, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_67 = x_48;
} else {
 lean_dec_ref(x_48);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
}
}
}
else
{
uint8_t x_70; 
x_70 = l_Lean_getPPProofsWithType(x_14);
lean_dec(x_14);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_71 = lean_box(0);
if (lean_is_scalar(x_13)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_13;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_17);
return x_72;
}
else
{
uint8_t x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_13);
x_73 = 0;
x_74 = lean_box(x_73);
x_75 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_75, 0, x_74);
x_76 = 1;
x_77 = lean_box(x_76);
x_78 = lean_box(x_76);
x_79 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg___boxed), 10, 3);
lean_closure_set(x_79, 0, x_77);
lean_closure_set(x_79, 1, x_78);
lean_closure_set(x_79, 2, x_75);
x_80 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___spec__1(x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_80, 0);
lean_dec(x_82);
x_83 = lean_box(0);
lean_ctor_set(x_80, 0, x_83);
return x_80;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_80);
if (x_87 == 0)
{
return x_80;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_80, 0);
x_89 = lean_ctor_get(x_80, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_80);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Delaborator.topDownAnalyze", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("false", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("true", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__1;
x_10 = l_Lean_Core_checkMaxHeartbeats(x_9, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_44 = lean_st_ref_get(x_7, x_11);
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
x_13 = x_49;
x_14 = x_48;
goto block_43;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_dec(x_44);
x_51 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__4(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_unbox(x_52);
lean_dec(x_52);
x_13 = x_54;
x_14 = x_53;
goto block_43;
}
block_43:
{
if (x_13 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
return x_16;
}
else
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_17 == 0)
{
lean_object* x_41; 
x_41 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__4;
x_19 = x_41;
goto block_40;
}
else
{
lean_object* x_42; 
x_42 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__7;
x_19 = x_42;
goto block_40;
}
block_40:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__8;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__3;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
if (x_18 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__6;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
x_29 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3(x_12, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___lambda__1(x_1, x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__9;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_22);
x_36 = l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3(x_12, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___lambda__1(x_1, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_38);
return x_39;
}
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_10);
if (x_55 == 0)
{
return x_10;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_10, 0);
x_57 = lean_ctor_get(x_10, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_10);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
static lean_object* _init_l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__10___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__10___rarg___lambda__1), 9, 3);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_1, x_2, x_3, x_12, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__10___rarg), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_expr_instantiate1(x_1, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___spec__2(x_11, x_12, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.PrettyPrinter.Delaborator.SubExpr", 38);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.PrettyPrinter.Delaborator.SubExpr.withLetBody", 50);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__1;
x_2 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(75u);
x_4 = lean_unsigned_to_nat(38u);
x_5 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__3;
x_14 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_2);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__3;
x_17 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__3(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_2);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__3;
x_20 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__4(x_1, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
return x_20;
}
case 3:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_2);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__3;
x_23 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__5(x_1, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_23;
}
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_2);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__3;
x_26 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__6(x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
return x_26;
}
case 5:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_2);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_dec(x_10);
x_28 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__3;
x_29 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__7(x_1, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
return x_29;
}
case 6:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_11);
lean_dec(x_2);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_dec(x_10);
x_31 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__3;
x_32 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__8(x_1, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
return x_32;
}
case 7:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_11);
lean_dec(x_2);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_dec(x_10);
x_34 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__3;
x_35 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__9(x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
return x_35;
}
case 8:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_1);
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_dec(x_10);
x_37 = lean_ctor_get(x_11, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_11, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_11, 3);
lean_inc(x_40);
lean_dec(x_11);
x_41 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___lambda__1), 10, 2);
lean_closure_set(x_41, 0, x_40);
lean_closure_set(x_41, 1, x_2);
x_42 = l_Lean_Meta_withLetDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__10___rarg(x_37, x_38, x_39, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
return x_42;
}
case 9:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_11);
lean_dec(x_2);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_dec(x_10);
x_44 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__3;
x_45 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__11(x_1, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
return x_45;
}
case 10:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_11);
lean_dec(x_2);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
lean_dec(x_10);
x_47 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__3;
x_48 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__12(x_1, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_46);
return x_48;
}
default: 
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_11);
lean_dec(x_2);
x_49 = lean_ctor_get(x_10, 1);
lean_inc(x_49);
lean_dec(x_10);
x_50 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__3;
x_51 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__13(x_1, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_49);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_SubExpr_Pos_push(x_13, x_2);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_4, 0, x_15);
x_16 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
else
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_18 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 1);
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 2);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 3);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_SubExpr_Pos_push(x_22, x_2);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_17);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 1, x_18);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 2, x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 3, x_20);
x_26 = lean_apply_7(x_3, x_25, x_5, x_6, x_7, x_8, x_9, x_10);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.PrettyPrinter.Delaborator.SubExpr.withLetVarType", 53);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__1;
x_2 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__1;
x_3 = lean_unsigned_to_nat(67u);
x_4 = lean_unsigned_to_nat(38u);
x_5 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__2;
x_14 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__15(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_2);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__2;
x_17 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__16(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_2);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__2;
x_20 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__17(x_1, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
return x_20;
}
case 3:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_2);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__2;
x_23 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__18(x_1, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_23;
}
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_2);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__2;
x_26 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__19(x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
return x_26;
}
case 5:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_2);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_dec(x_10);
x_28 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__2;
x_29 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__20(x_1, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
return x_29;
}
case 6:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_11);
lean_dec(x_2);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_dec(x_10);
x_31 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__2;
x_32 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__21(x_1, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
return x_32;
}
case 7:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_11);
lean_dec(x_2);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_dec(x_10);
x_34 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__2;
x_35 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__22(x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
return x_35;
}
case 8:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_1);
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_dec(x_10);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__23(x_37, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
return x_39;
}
case 9:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_11);
lean_dec(x_2);
x_40 = lean_ctor_get(x_10, 1);
lean_inc(x_40);
lean_dec(x_10);
x_41 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__2;
x_42 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__24(x_1, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
return x_42;
}
case 10:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_11);
lean_dec(x_2);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_dec(x_10);
x_44 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__2;
x_45 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__25(x_1, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
return x_45;
}
default: 
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_11);
lean_dec(x_2);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
lean_dec(x_10);
x_47 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__2;
x_48 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__26(x_1, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_46);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__34(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__35(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__36(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__38(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.PrettyPrinter.Delaborator.SubExpr.withLetValue", 51);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__1;
x_2 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__1;
x_3 = lean_unsigned_to_nat(71u);
x_4 = lean_unsigned_to_nat(38u);
x_5 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__2;
x_14 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__28(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_2);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__2;
x_17 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__29(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_2);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__2;
x_20 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__30(x_1, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
return x_20;
}
case 3:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_2);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__2;
x_23 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__31(x_1, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_23;
}
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_2);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__2;
x_26 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__32(x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
return x_26;
}
case 5:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_2);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_dec(x_10);
x_28 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__2;
x_29 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__33(x_1, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
return x_29;
}
case 6:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_11);
lean_dec(x_2);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_dec(x_10);
x_31 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__2;
x_32 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__34(x_1, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
return x_32;
}
case 7:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_11);
lean_dec(x_2);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_dec(x_10);
x_34 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__2;
x_35 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__35(x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
return x_35;
}
case 8:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_1);
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_dec(x_10);
x_37 = lean_ctor_get(x_11, 2);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_unsigned_to_nat(1u);
x_39 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___spec__2(x_37, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
return x_39;
}
case 9:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_11);
lean_dec(x_2);
x_40 = lean_ctor_get(x_10, 1);
lean_inc(x_40);
lean_dec(x_10);
x_41 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__2;
x_42 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__36(x_1, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
return x_42;
}
case 10:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_11);
lean_dec(x_2);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_dec(x_10);
x_44 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__2;
x_45 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__37(x_1, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
return x_45;
}
default: 
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_11);
lean_dec(x_2);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
lean_dec(x_10);
x_47 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__2;
x_48 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__38(x_1, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_46);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l_instInhabitedPUnit;
x_13 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1(x_12, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.PrettyPrinter.Delaborator.TopDownAnalyze.analyze.analyzeLet", 64);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__1;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___closed__1;
x_3 = lean_unsigned_to_nat(461u);
x_4 = lean_unsigned_to_nat(46u);
x_5 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___lambda__1), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 8)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(10u);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp(x_11, x_12, x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___closed__3;
x_18 = lean_unbox(x_15);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = l_Lean_getPPAnalysisLetVarType___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_19, x_1, x_2, x_3, x_4, x_5, x_6, x_16);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_box(x_22);
lean_inc(x_24);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg___boxed), 10, 3);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_27);
lean_closure_set(x_28, 2, x_24);
x_29 = l_instInhabitedPUnit;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_30 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14(x_29, x_28, x_1, x_2, x_3, x_4, x_5, x_6, x_21);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(x_25);
x_33 = lean_box(x_25);
x_34 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg___boxed), 10, 3);
lean_closure_set(x_34, 0, x_32);
lean_closure_set(x_34, 1, x_33);
lean_closure_set(x_34, 2, x_24);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_35 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27(x_29, x_34, x_1, x_2, x_3, x_4, x_5, x_6, x_31);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_apply_8(x_17, x_36, x_1, x_2, x_3, x_4, x_5, x_6, x_37);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
uint8_t x_43; 
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
uint8_t x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_47 = 0;
x_48 = lean_box(x_47);
x_49 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = 1;
x_51 = lean_box(x_50);
x_52 = lean_box(x_50);
x_53 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg___boxed), 10, 3);
lean_closure_set(x_53, 0, x_51);
lean_closure_set(x_53, 1, x_52);
lean_closure_set(x_53, 2, x_49);
x_54 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_55 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_56 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 3);
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
x_58 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_54);
lean_ctor_set_uint8(x_58, sizeof(void*)*1 + 1, x_55);
lean_ctor_set_uint8(x_58, sizeof(void*)*1 + 2, x_50);
lean_ctor_set_uint8(x_58, sizeof(void*)*1 + 3, x_56);
x_59 = l_instInhabitedPUnit;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_60 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27(x_59, x_53, x_58, x_2, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_apply_8(x_17, x_61, x_1, x_2, x_3, x_4, x_5, x_6, x_62);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_60);
if (x_64 == 0)
{
return x_60;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_60, 0);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_60);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_14);
if (x_68 == 0)
{
return x_14;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_14, 0);
x_70 = lean_ctor_get(x_14, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_14);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_9);
x_72 = lean_ctor_get(x_8, 1);
lean_inc(x_72);
lean_dec(x_8);
x_73 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___closed__2;
x_74 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1(x_73, x_1, x_2, x_3, x_4, x_5, x_6, x_72);
return x_74;
}
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.PrettyPrinter.Delaborator.SubExpr.withMDataExpr", 52);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__1;
x_2 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__1;
x_3 = lean_unsigned_to_nat(63u);
x_4 = lean_unsigned_to_nat(35u);
x_5 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__2;
x_14 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__2(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_2);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__2;
x_17 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__3(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_2);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__2;
x_20 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__4(x_1, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
return x_20;
}
case 3:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_2);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__2;
x_23 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__5(x_1, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_23;
}
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_2);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__2;
x_26 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__6(x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
return x_26;
}
case 5:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_2);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_dec(x_10);
x_28 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__2;
x_29 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__7(x_1, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
return x_29;
}
case 6:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_11);
lean_dec(x_2);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_dec(x_10);
x_31 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__2;
x_32 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__8(x_1, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
return x_32;
}
case 7:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_11);
lean_dec(x_2);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_dec(x_10);
x_34 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__2;
x_35 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__9(x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
return x_35;
}
case 8:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
lean_dec(x_2);
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_dec(x_10);
x_37 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__2;
x_38 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__10(x_1, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
return x_38;
}
case 9:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_11);
lean_dec(x_2);
x_39 = lean_ctor_get(x_10, 1);
lean_inc(x_39);
lean_dec(x_10);
x_40 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__2;
x_41 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__11(x_1, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_39);
return x_41;
}
case 10:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_1);
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_dec(x_10);
x_44 = lean_ctor_get(x_11, 1);
lean_inc(x_44);
lean_dec(x_11);
x_45 = !lean_is_exclusive(x_3);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_3, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_42);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_42, 0);
lean_dec(x_48);
lean_ctor_set(x_42, 0, x_44);
x_49 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
lean_dec(x_42);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_3, 0, x_51);
x_52 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
return x_52;
}
}
else
{
uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_54 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_55 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 2);
x_56 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 3);
lean_dec(x_3);
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_58 = x_42;
} else {
 lean_dec_ref(x_42);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_44);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_53);
lean_ctor_set_uint8(x_60, sizeof(void*)*1 + 1, x_54);
lean_ctor_set_uint8(x_60, sizeof(void*)*1 + 2, x_55);
lean_ctor_set_uint8(x_60, sizeof(void*)*1 + 3, x_56);
x_61 = lean_apply_7(x_2, x_60, x_4, x_5, x_6, x_7, x_8, x_43);
return x_61;
}
}
default: 
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_11);
lean_dec(x_2);
x_62 = lean_ctor_get(x_10, 1);
lean_inc(x_62);
lean_dec(x_10);
x_63 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__2;
x_64 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__12(x_1, x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_62);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = l_instInhabitedPUnit;
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1(x_11, x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1;
x_11 = l_instInhabited___rarg(x_10, x_1);
x_12 = lean_panic_fn(x_11, x_2);
x_13 = lean_apply_7(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.PrettyPrinter.Delaborator.SubExpr.withProj", 47);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__1;
x_2 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__1;
x_3 = lean_unsigned_to_nat(59u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__2;
x_14 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__2(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_2);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__2;
x_17 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__3(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_2);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__2;
x_20 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__4(x_1, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
return x_20;
}
case 3:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_2);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__2;
x_23 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__5(x_1, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_23;
}
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_2);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__2;
x_26 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__6(x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
return x_26;
}
case 5:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_2);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_dec(x_10);
x_28 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__2;
x_29 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__7(x_1, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
return x_29;
}
case 6:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_11);
lean_dec(x_2);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_dec(x_10);
x_31 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__2;
x_32 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__8(x_1, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
return x_32;
}
case 7:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_11);
lean_dec(x_2);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_dec(x_10);
x_34 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__2;
x_35 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__9(x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
return x_35;
}
case 8:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
lean_dec(x_2);
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_dec(x_10);
x_37 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__2;
x_38 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__10(x_1, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
return x_38;
}
case 9:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_11);
lean_dec(x_2);
x_39 = lean_ctor_get(x_10, 1);
lean_inc(x_39);
lean_dec(x_10);
x_40 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__2;
x_41 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__11(x_1, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_39);
return x_41;
}
case 10:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_11);
lean_dec(x_2);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_dec(x_10);
x_43 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__2;
x_44 = l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__12(x_1, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_42);
return x_44;
}
default: 
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_1);
x_45 = lean_ctor_get(x_10, 1);
lean_inc(x_45);
lean_dec(x_10);
x_46 = lean_ctor_get(x_11, 2);
lean_inc(x_46);
lean_dec(x_11);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___spec__2(x_46, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_45);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = l_instInhabitedPUnit;
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1(x_11, x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_bindingDomain_x21(x_10);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__23(x_12, x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__3___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__10___rarg___lambda__1), 9, 3);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_12, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__3___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Expr_bindingBody_x21(x_1);
lean_dec(x_1);
x_12 = lean_expr_instantiate1(x_11, x_3);
lean_dec(x_3);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___spec__2(x_12, x_13, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_binderInfo(x_11);
x_14 = l_Lean_Expr_bindingDomain_x21(x_11);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__2___lambda__1), 10, 2);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_2);
x_16 = l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__3___rarg(x_1, x_13, x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_box(x_9);
lean_inc(x_11);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg___boxed), 10, 3);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__1(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__2(x_18, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___lambda__1), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___closed__1;
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_8(x_8, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_apply_8(x_8, x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzePi(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_box(x_8);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg___boxed), 10, 3);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__1(x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__2(x_17, x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_apply_8(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___spec__1___rarg), 9, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = lean_infer_type(x_10, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_SubExpr_Pos_typeCoord;
x_16 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__23(x_13, x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Expr_getAppFn(x_11);
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Expr_getAppNumArgsAux(x_14, x_17);
x_19 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams___closed__1;
lean_inc(x_18);
x_20 = lean_mk_array(x_18, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_18, x_21);
lean_dec(x_18);
x_23 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_14, x_20, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged), 9, 2);
lean_closure_set(x_24, 0, x_16);
lean_closure_set(x_24, 1, x_23);
x_25 = 1;
x_26 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg(x_1, x_25, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = 1;
x_13 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg(x_12, x_9, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___lambda__1___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structureInstanceTypes", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__2;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool), 8, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___lambda__2___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(10u);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp(x_10, x_12, x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__1;
if (x_8 == 0)
{
uint8_t x_51; 
x_51 = lean_unbox(x_15);
lean_dec(x_15);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_52 = l_Lean_getPPAnalysisNeedsType___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_53 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_52, x_1, x_2, x_3, x_4, x_5, x_6, x_16);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = 0;
x_56 = lean_box(x_55);
x_57 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_57, 0, x_56);
x_58 = 1;
x_59 = lean_box(x_58);
x_60 = lean_box(x_55);
x_61 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg___boxed), 10, 3);
lean_closure_set(x_61, 0, x_59);
lean_closure_set(x_61, 1, x_60);
lean_closure_set(x_61, 2, x_57);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_62 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___spec__2(x_61, x_1, x_2, x_3, x_4, x_5, x_6, x_54);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_box(0);
x_65 = lean_box(x_58);
x_66 = lean_apply_9(x_17, x_65, x_64, x_1, x_2, x_3, x_4, x_5, x_6, x_63);
return x_66;
}
else
{
uint8_t x_67; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_62);
if (x_67 == 0)
{
return x_62;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_62, 0);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_62);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; 
x_71 = lean_box(0);
x_18 = x_71;
goto block_50;
}
}
else
{
lean_object* x_72; 
lean_dec(x_15);
x_72 = lean_box(0);
x_18 = x_72;
goto block_50;
}
block_50:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
lean_dec(x_18);
x_19 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
if (x_8 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = l_Lean_PrettyPrinter_Delaborator_isStructureInstance(x_20, x_3, x_4, x_5, x_6, x_21);
lean_dec(x_20);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_unbox(x_42);
lean_dec(x_42);
x_22 = x_44;
x_23 = x_43;
goto block_40;
}
else
{
uint8_t x_45; 
x_45 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
if (x_45 == 0)
{
lean_dec(x_20);
x_22 = x_45;
x_23 = x_21;
goto block_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = l_Lean_PrettyPrinter_Delaborator_isStructureInstance(x_20, x_3, x_4, x_5, x_6, x_21);
lean_dec(x_20);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_unbox(x_47);
lean_dec(x_47);
x_22 = x_49;
x_23 = x_48;
goto block_40;
}
}
block_40:
{
if (x_22 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_box(0);
x_25 = lean_box(x_8);
x_26 = lean_apply_9(x_17, x_25, x_24, x_1, x_2, x_3, x_4, x_5, x_6, x_23);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__4;
x_28 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__5;
x_29 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___spec__1___rarg), 9, 2);
lean_closure_set(x_29, 0, x_27);
lean_closure_set(x_29, 1, x_28);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_30 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___spec__2(x_29, x_1, x_2, x_3, x_4, x_5, x_6, x_23);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = 1;
x_33 = lean_box(0);
x_34 = lean_box(x_32);
x_35 = lean_apply_9(x_17, x_34, x_33, x_1, x_2, x_3, x_4, x_5, x_6, x_31);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_30);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_14);
if (x_73 == 0)
{
return x_14;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_14, 0);
x_75 = lean_ctor_get(x_14, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_14);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Subtype", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mk", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__2;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_7);
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
x_16 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_8, x_9, x_10, x_11, x_12, x_13, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_maybeAddBlockImplicit___spec__1(x_8, x_9, x_10, x_11, x_12, x_13, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_getPPAnalyzeTrustSubst(x_15);
x_26 = lean_array_get_size(x_1);
x_27 = 0;
x_28 = lean_box(x_27);
x_29 = lean_mk_array(x_26, x_28);
x_30 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__2;
lean_inc_n(x_29, 3);
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set(x_31, 4, x_30);
if (x_25 == 0)
{
uint8_t x_58; 
lean_dec(x_17);
x_58 = l_Lean_getPPAnalyzeTrustCoe(x_15);
if (x_58 == 0)
{
uint8_t x_59; 
lean_dec(x_20);
x_59 = l_Lean_getPPAnalyzeTrustSubtypeMk(x_15);
lean_dec(x_15);
if (x_59 == 0)
{
lean_dec(x_23);
x_32 = x_27;
goto block_57;
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__4;
x_61 = lean_unsigned_to_nat(4u);
x_62 = l_Lean_Expr_isAppOfArity(x_23, x_60, x_61);
lean_dec(x_23);
x_32 = x_62;
goto block_57;
}
}
else
{
uint8_t x_63; 
x_63 = l_Lean_PrettyPrinter_Delaborator_isCoe(x_20);
lean_dec(x_20);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = l_Lean_getPPAnalyzeTrustSubtypeMk(x_15);
lean_dec(x_15);
if (x_64 == 0)
{
lean_dec(x_23);
x_32 = x_27;
goto block_57;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__4;
x_66 = lean_unsigned_to_nat(4u);
x_67 = l_Lean_Expr_isAppOfArity(x_23, x_65, x_66);
lean_dec(x_23);
x_32 = x_67;
goto block_57;
}
}
else
{
uint8_t x_68; 
lean_dec(x_23);
lean_dec(x_15);
x_68 = 1;
x_32 = x_68;
goto block_57;
}
}
}
else
{
uint8_t x_69; 
x_69 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike(x_17);
lean_dec(x_17);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_getPPAnalyzeTrustCoe(x_15);
if (x_70 == 0)
{
uint8_t x_71; 
lean_dec(x_20);
x_71 = l_Lean_getPPAnalyzeTrustSubtypeMk(x_15);
lean_dec(x_15);
if (x_71 == 0)
{
lean_dec(x_23);
x_32 = x_27;
goto block_57;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__4;
x_73 = lean_unsigned_to_nat(4u);
x_74 = l_Lean_Expr_isAppOfArity(x_23, x_72, x_73);
lean_dec(x_23);
x_32 = x_74;
goto block_57;
}
}
else
{
uint8_t x_75; 
x_75 = l_Lean_PrettyPrinter_Delaborator_isCoe(x_20);
lean_dec(x_20);
if (x_75 == 0)
{
uint8_t x_76; 
x_76 = l_Lean_getPPAnalyzeTrustSubtypeMk(x_15);
lean_dec(x_15);
if (x_76 == 0)
{
lean_dec(x_23);
x_32 = x_27;
goto block_57;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__4;
x_78 = lean_unsigned_to_nat(4u);
x_79 = l_Lean_Expr_isAppOfArity(x_23, x_77, x_78);
lean_dec(x_23);
x_32 = x_79;
goto block_57;
}
}
else
{
uint8_t x_80; 
lean_dec(x_23);
lean_dec(x_15);
x_80 = 1;
x_32 = x_80;
goto block_57;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_15);
x_81 = 1;
x_32 = x_81;
goto block_57;
}
}
block_57:
{
lean_object* x_33; lean_object* x_34; 
lean_inc(x_1);
lean_inc(x_2);
x_33 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_3);
lean_ctor_set(x_33, 2, x_1);
lean_ctor_set(x_33, 3, x_4);
lean_ctor_set(x_33, 4, x_5);
lean_ctor_set_uint8(x_33, sizeof(void*)*5, x_32);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_34 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore(x_33, x_31, x_8, x_9, x_10, x_11, x_12, x_13, x_24);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_34, 1);
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = l_Array_isEmpty___rarg(x_6);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_Array_isEmpty___rarg(x_1);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_free_object(x_34);
x_40 = l_Lean_mkAppN(x_2, x_1);
x_41 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged(x_40, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_36);
return x_41;
}
else
{
lean_object* x_42; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_box(0);
lean_ctor_set(x_34, 0, x_42);
return x_34;
}
}
else
{
lean_object* x_43; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_box(0);
lean_ctor_set(x_34, 0, x_43);
return x_34;
}
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_dec(x_34);
x_45 = l_Array_isEmpty___rarg(x_6);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = l_Array_isEmpty___rarg(x_1);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = l_Lean_mkAppN(x_2, x_1);
x_48 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged(x_47, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_44);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_44);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_34);
if (x_53 == 0)
{
return x_34;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_34, 0);
x_55 = lean_ctor_get(x_34, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_34);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = lean_infer_type(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars(x_11, x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_2);
x_17 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_16);
lean_inc(x_14);
x_18 = l_Lean_Meta_forallMetaBoundedTelescope(x_14, x_16, x_17, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_array_get_size(x_22);
lean_inc(x_25);
lean_inc(x_2);
x_26 = l_Array_extract___rarg(x_2, x_25, x_16);
x_27 = l_Array_shrink___rarg(x_2, x_25);
lean_dec(x_25);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1(x_27, x_1, x_14, x_22, x_23, x_26, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_inc(x_27);
lean_inc(x_1);
x_31 = l_Lean_mkAppN(x_1, x_27);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_32 = lean_infer_type(x_31, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_35 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_33, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1(x_27, x_1, x_14, x_22, x_23, x_26, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
else
{
uint8_t x_43; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_32);
if (x_43 == 0)
{
return x_32;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_32, 0);
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_32);
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
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_18);
if (x_47 == 0)
{
return x_18;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_18, 0);
x_49 = lean_ctor_get(x_18, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_18);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_10);
if (x_51 == 0)
{
return x_10;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_10, 0);
x_53 = lean_ctor_get(x_10, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_10);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_1, x_18);
lean_dec(x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_20 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_25 = lean_box(0);
x_1 = x_19;
x_2 = x_24;
x_5 = x_25;
x_7 = x_23;
x_14 = x_22;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
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
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_7);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_14);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_7);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_14);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_checkOutParams(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_18 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectHigherOrders(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_26 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectTrivialBottomUps(x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = 1;
x_31 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_32 = l_Lean_Meta_processPostponed(x_30, x_31, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_34 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic(x_1, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_38 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn(x_1, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
x_43 = lean_array_get_size(x_42);
lean_dec(x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_43);
x_47 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore___spec__1(x_43, x_44, x_43, x_45, x_46, x_1, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
lean_dec(x_43);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit(x_1, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_49);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_47, 0);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_47);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_38);
if (x_56 == 0)
{
return x_38;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_38, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_38);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_34);
if (x_60 == 0)
{
return x_34;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_34, 0);
x_62 = lean_ctor_get(x_34, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_34);
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
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_32);
if (x_64 == 0)
{
return x_32;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_32, 0);
x_66 = lean_ctor_get(x_32, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_32);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_26);
if (x_68 == 0)
{
return x_26;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_26, 0);
x_70 = lean_ctor_get(x_26, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_26);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_22);
if (x_72 == 0)
{
return x_22;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_22, 0);
x_74 = lean_ctor_get(x_22, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_22);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_18);
if (x_76 == 0)
{
return x_18;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_18, 0);
x_78 = lean_ctor_get(x_18, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_18);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_14);
if (x_80 == 0)
{
return x_14;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_14, 0);
x_82 = lean_ctor_get(x_14, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_14);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_10);
if (x_84 == 0)
{
return x_10;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_10, 0);
x_86 = lean_ctor_get(x_10, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_10);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_nameNotRoundtrippable(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_SubExpr_Pos_push(x_15, x_2);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_6, 0, x_17);
x_18 = lean_apply_9(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
else
{
uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_20 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 1);
x_21 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 2);
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*1 + 3);
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_23);
lean_dec(x_6);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_SubExpr_Pos_push(x_24, x_2);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_19);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 1, x_20);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 2, x_21);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 3, x_22);
x_28 = lean_apply_9(x_3, x_4, x_5, x_27, x_7, x_8, x_9, x_10, x_11, x_12);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___spec__1___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = lean_infer_type(x_14, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_SubExpr_Pos_typeCoord;
x_20 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__3(x_17, x_19, x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___spec__1___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Expr_getAppNumArgsAux(x_15, x_17);
x_19 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams___closed__1;
lean_inc(x_18);
x_20 = lean_mk_array(x_18, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_18, x_21);
lean_dec(x_18);
x_23 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_15, x_20, x_22);
x_24 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__2___rarg(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_array_get_size(x_23);
x_30 = l_Lean_SubExpr_Pos_pushNaryArg(x_29, x_1, x_27);
lean_dec(x_27);
lean_dec(x_29);
x_31 = !lean_is_exclusive(x_5);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_5, 0);
lean_dec(x_32);
x_33 = l_Lean_instInhabitedExpr;
x_34 = lean_array_get(x_33, x_23, x_1);
lean_dec(x_23);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_5, 0, x_35);
x_36 = lean_apply_9(x_2, x_3, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
return x_36;
}
else
{
uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_38 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_39 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_40 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
lean_dec(x_5);
x_41 = l_Lean_instInhabitedExpr;
x_42 = lean_array_get(x_41, x_23, x_1);
lean_dec(x_23);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_30);
x_44 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_37);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 1, x_38);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 2, x_39);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 3, x_40);
x_45 = lean_apply_9(x_2, x_3, x_28, x_44, x_6, x_7, x_8, x_9, x_10, x_26);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = 1;
x_12 = 0;
x_13 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg(x_11, x_12, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
x_14 = l_Lean_instInhabitedBinderInfo;
x_15 = lean_box(x_14);
x_16 = lean_array_get(x_15, x_1, x_2);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
x_18 = 3;
x_19 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_362_(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_20 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = l_Lean_getPPInstanceTypes(x_13);
lean_dec(x_13);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_24 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = 0;
x_28 = lean_box(x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___lambda__1___boxed), 10, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__2(x_30, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
lean_ctor_set(x_33, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_31, 0, x_39);
return x_31;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_31);
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
x_44 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1;
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_31);
if (x_47 == 0)
{
return x_31;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_31, 0);
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_31);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
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
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_6, x_5);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_4, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_8);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_4, x_21);
lean_dec(x_4);
x_23 = lean_ctor_get(x_10, 3);
lean_inc(x_23);
x_24 = l_instInhabitedBool;
x_25 = lean_box(x_24);
x_26 = lean_array_get(x_25, x_23, x_5);
lean_dec(x_23);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = l_Lean_Expr_getAppNumArgsAux(x_1, x_19);
x_29 = lean_nat_add(x_28, x_5);
lean_dec(x_28);
x_30 = l_Lean_getPPAnalysisSkip___closed__1;
lean_inc(x_3);
x_31 = lean_name_mk_string(x_3, x_30);
x_32 = l_Lean_getPPAnalysisHole___closed__1;
x_33 = lean_name_mk_string(x_31, x_32);
x_34 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___lambda__3___boxed), 10, 1);
lean_closure_set(x_34, 0, x_33);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_35 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__4(x_29, x_34, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_29);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_40 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___lambda__2(x_2, x_5, x_38, x_9, x_39, x_11, x_12, x_13, x_14, x_15, x_16, x_37);
lean_dec(x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_40, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
lean_dec(x_42);
lean_ctor_set(x_41, 0, x_47);
return x_40;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set(x_40, 0, x_50);
return x_40;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_40, 1);
lean_inc(x_51);
lean_dec(x_40);
x_52 = lean_ctor_get(x_41, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_53 = x_41;
} else {
 lean_dec_ref(x_41);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_42, 0);
lean_inc(x_54);
lean_dec(x_42);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_51);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_40, 1);
lean_inc(x_57);
lean_dec(x_40);
x_58 = lean_ctor_get(x_41, 1);
lean_inc(x_58);
lean_dec(x_41);
x_59 = lean_ctor_get(x_42, 0);
lean_inc(x_59);
lean_dec(x_42);
x_60 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_22;
x_5 = x_60;
x_8 = x_59;
x_10 = x_58;
x_17 = x_57;
goto _start;
}
}
else
{
uint8_t x_62; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_40);
if (x_62 == 0)
{
return x_40;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_40, 0);
x_64 = lean_ctor_get(x_40, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_40);
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
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_35);
if (x_66 == 0)
{
return x_35;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_35, 0);
x_68 = lean_ctor_get(x_35, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_35);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_box(0);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_71 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___lambda__2(x_2, x_5, x_70, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_71);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_71, 0);
lean_dec(x_75);
x_76 = !lean_is_exclusive(x_72);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_72, 0);
lean_dec(x_77);
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
lean_dec(x_73);
lean_ctor_set(x_72, 0, x_78);
return x_71;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_dec(x_72);
x_80 = lean_ctor_get(x_73, 0);
lean_inc(x_80);
lean_dec(x_73);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
lean_ctor_set(x_71, 0, x_81);
return x_71;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_71, 1);
lean_inc(x_82);
lean_dec(x_71);
x_83 = lean_ctor_get(x_72, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_84 = x_72;
} else {
 lean_dec_ref(x_72);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_73, 0);
lean_inc(x_85);
lean_dec(x_73);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_82);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_71, 1);
lean_inc(x_88);
lean_dec(x_71);
x_89 = lean_ctor_get(x_72, 1);
lean_inc(x_89);
lean_dec(x_72);
x_90 = lean_ctor_get(x_73, 0);
lean_inc(x_90);
lean_dec(x_73);
x_91 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_22;
x_5 = x_91;
x_8 = x_90;
x_10 = x_89;
x_17 = x_88;
goto _start;
}
}
else
{
uint8_t x_93; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_93 = !lean_is_exclusive(x_71);
if (x_93 == 0)
{
return x_71;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_71, 0);
x_95 = lean_ctor_get(x_71, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_71);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_8);
lean_ctor_set(x_97, 1, x_10);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_17);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_8);
lean_ctor_set(x_99, 1, x_10);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_17);
return x_100;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("explicit", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__2;
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 4);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
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
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_14, x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
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
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
else
{
size_t x_24; size_t x_25; uint8_t x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_26 = l_Array_anyMUnsafe_any___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__1(x_13, x_24, x_25);
lean_dec(x_13);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_9);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_31 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_array_get_size(x_11);
lean_dec(x_11);
x_34 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__2;
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_box(0);
lean_inc(x_33);
x_37 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5(x_10, x_12, x_34, x_33, x_15, x_33, x_35, x_36, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
lean_dec(x_33);
lean_dec(x_12);
lean_dec(x_10);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_36);
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_37, 0, x_43);
return x_37;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_37, 0);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_37);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_36);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
else
{
uint8_t x_50; 
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_hBinOpHeuristic___spec__1___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Expr_getAppNumArgsAux(x_15, x_17);
x_19 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams___closed__1;
lean_inc(x_18);
x_20 = lean_mk_array(x_18, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_18, x_21);
lean_dec(x_18);
x_23 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_15, x_20, x_22);
x_24 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic___spec__2___rarg(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_array_get_size(x_23);
x_30 = l_Lean_SubExpr_Pos_pushNaryArg(x_29, x_1, x_27);
lean_dec(x_27);
lean_dec(x_29);
x_31 = !lean_is_exclusive(x_5);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_5, 0);
lean_dec(x_32);
x_33 = l_Lean_instInhabitedExpr;
x_34 = lean_array_get(x_33, x_23, x_1);
lean_dec(x_23);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_5, 0, x_35);
x_36 = lean_apply_9(x_2, x_3, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
return x_36;
}
else
{
uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_38 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_39 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_40 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
lean_dec(x_5);
x_41 = l_Lean_instInhabitedExpr;
x_42 = lean_array_get(x_41, x_23, x_1);
lean_dec(x_23);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_30);
x_44 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_37);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 1, x_38);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 2, x_39);
lean_ctor_set_uint8(x_44, sizeof(void*)*1 + 3, x_40);
x_45 = lean_apply_9(x_2, x_3, x_28, x_44, x_6, x_7, x_8, x_9, x_10, x_26);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify(x_1, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_4);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = l_instInhabitedBool;
x_16 = lean_box(x_15);
x_17 = lean_array_get(x_16, x_14, x_3);
lean_dec(x_3);
lean_dec(x_14);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__1(x_1, x_2, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_20;
}
else
{
lean_object* x_21; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_21 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_typeUnknown(x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 0;
x_25 = lean_box(x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_unbox(x_22);
lean_dec(x_22);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; 
x_28 = 1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_29 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg(x_28, x_28, x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__1(x_1, x_2, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
lean_dec(x_5);
lean_dec(x_30);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
uint8_t x_37; lean_object* x_38; 
x_37 = 1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_38 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_withKnowing___rarg(x_24, x_37, x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_23);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__1(x_1, x_2, x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_40);
lean_dec(x_5);
lean_dec(x_39);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
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
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_21);
if (x_46 == 0)
{
return x_21;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_21, 0);
x_48 = lean_ctor_get(x_21, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_21);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_6, 3);
x_16 = lean_box(x_3);
x_17 = lean_array_set(x_15, x_1, x_16);
lean_ctor_set(x_6, 3, x_17);
x_18 = lean_box(0);
x_19 = lean_apply_10(x_2, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 2);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 4);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_25 = lean_box(x_3);
x_26 = lean_array_set(x_23, x_1, x_25);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_27, 4, x_24);
x_28 = lean_box(0);
x_29 = lean_apply_10(x_2, x_28, x_5, x_27, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_17 = l_Lean_Meta_checkpointDefEq___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq___spec__1(x_15, x_3, x_16, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_mvarName(x_1, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_24 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg(x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(x_4);
x_30 = lean_apply_11(x_2, x_29, x_27, x_6, x_28, x_8, x_9, x_10, x_11, x_12, x_13, x_26);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_dec(x_17);
x_36 = l_Lean_getPPAnalysisSkip___closed__4;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_37 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_36, x_8, x_9, x_10, x_11, x_12, x_13, x_35);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_box(0);
x_40 = lean_box(x_16);
x_41 = lean_apply_11(x_2, x_40, x_39, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_38);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_17);
if (x_42 == 0)
{
return x_17;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_17, 0);
x_44 = lean_ctor_get(x_17, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_17);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_5);
lean_dec(x_3);
x_46 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_mvarName(x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_49 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg(x_47, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_box(x_4);
x_55 = lean_apply_11(x_2, x_54, x_52, x_6, x_53, x_8, x_9, x_10, x_11, x_12, x_13, x_51);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_46);
if (x_56 == 0)
{
return x_46;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_46, 0);
x_58 = lean_ctor_get(x_46, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_46);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
x_21 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 1);
x_22 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 2);
x_23 = lean_ctor_get_uint8(x_13, sizeof(void*)*1 + 3);
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_25 = x_13;
} else {
 lean_dec_ref(x_13);
 x_25 = lean_box(0);
}
if (x_22 == 0)
{
uint8_t x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_246 = l_instInhabitedBool;
x_247 = lean_box(x_246);
x_248 = lean_array_get(x_247, x_10, x_4);
lean_dec(x_10);
x_249 = lean_unbox(x_248);
lean_dec(x_248);
x_26 = x_249;
goto block_245;
}
else
{
uint8_t x_250; 
lean_dec(x_10);
x_250 = 1;
x_26 = x_250;
goto block_245;
}
block_245:
{
lean_object* x_27; 
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 1, 4);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_20);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 1, x_21);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 2, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 3, x_23);
switch (x_1) {
case 0:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
lean_dec(x_8);
x_28 = lean_ctor_get(x_17, 2);
lean_inc(x_28);
lean_inc(x_2);
x_29 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(x_2, x_15, x_16, x_17, x_18, x_19);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_3);
x_32 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike(x_3, x_15, x_16, x_17, x_18, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_getPPAnalyzeExplicitHoles(x_28);
lean_dec(x_28);
if (x_35 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_66 = lean_box(x_35);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_12);
x_36 = x_67;
x_37 = x_34;
goto block_65;
}
else
{
uint8_t x_68; 
x_68 = lean_unbox(x_30);
lean_dec(x_30);
if (x_68 == 0)
{
if (x_26 == 0)
{
uint8_t x_69; 
x_69 = lean_unbox(x_33);
lean_dec(x_33);
if (x_69 == 0)
{
uint8_t x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = l_instInhabitedBool;
x_71 = lean_box(x_70);
x_72 = lean_array_get(x_71, x_6, x_4);
lean_dec(x_6);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
uint8_t x_74; lean_object* x_75; 
x_74 = 0;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_75 = l_Lean_Meta_checkpointDefEq___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkpointDefEq___spec__1(x_2, x_3, x_74, x_15, x_16, x_17, x_18, x_34);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_12);
x_36 = x_78;
x_37 = x_77;
goto block_65;
}
else
{
uint8_t x_79; 
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_79 = !lean_is_exclusive(x_75);
if (x_79 == 0)
{
return x_75;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_75, 0);
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_75);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_3);
lean_dec(x_2);
x_83 = 0;
x_84 = lean_box(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_12);
x_36 = x_85;
x_37 = x_34;
goto block_65;
}
}
else
{
uint8_t x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_86 = 0;
x_87 = lean_box(x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_12);
x_36 = x_88;
x_37 = x_34;
goto block_65;
}
}
else
{
uint8_t x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_89 = 0;
x_90 = lean_box(x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_12);
x_36 = x_91;
x_37 = x_34;
goto block_65;
}
}
else
{
uint8_t x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_92 = 0;
x_93 = lean_box(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_12);
x_36 = x_94;
x_37 = x_34;
goto block_65;
}
}
block_65:
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_40, 3);
x_43 = 1;
x_44 = lean_box(x_43);
x_45 = lean_array_set(x_42, x_4, x_44);
lean_dec(x_4);
lean_ctor_set(x_40, 3, x_45);
x_46 = lean_box(0);
x_47 = lean_apply_10(x_5, x_46, x_11, x_40, x_27, x_14, x_15, x_16, x_17, x_18, x_37);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_ctor_get(x_40, 0);
x_49 = lean_ctor_get(x_40, 1);
x_50 = lean_ctor_get(x_40, 2);
x_51 = lean_ctor_get(x_40, 3);
x_52 = lean_ctor_get(x_40, 4);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_40);
x_53 = 1;
x_54 = lean_box(x_53);
x_55 = lean_array_set(x_51, x_4, x_54);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_56, 0, x_48);
lean_ctor_set(x_56, 1, x_49);
lean_ctor_set(x_56, 2, x_50);
lean_ctor_set(x_56, 3, x_55);
lean_ctor_set(x_56, 4, x_52);
x_57 = lean_box(0);
x_58 = lean_apply_10(x_5, x_57, x_11, x_56, x_27, x_14, x_15, x_16, x_17, x_18, x_37);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_4);
x_59 = lean_ctor_get(x_36, 1);
lean_inc(x_59);
lean_dec(x_36);
x_60 = l_Lean_getPPAnalysisHole___closed__2;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_27);
x_61 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_60, x_27, x_14, x_15, x_16, x_17, x_18, x_37);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_apply_10(x_5, x_62, x_11, x_59, x_27, x_14, x_15, x_16, x_17, x_18, x_63);
return x_64;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_32);
if (x_95 == 0)
{
return x_32;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_32, 0);
x_97 = lean_ctor_get(x_32, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_32);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
case 1:
{
lean_object* x_99; lean_object* x_100; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_inc(x_2);
x_146 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(x_2, x_15, x_16, x_17, x_18, x_19);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_unbox(x_147);
if (x_148 == 0)
{
lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_147);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec(x_146);
x_150 = l_instInhabitedBool;
x_151 = lean_box(x_150);
x_152 = lean_array_get(x_151, x_8, x_4);
lean_dec(x_8);
x_153 = lean_unbox(x_152);
lean_dec(x_152);
x_154 = lean_box(x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_12);
x_99 = x_155;
x_100 = x_149;
goto block_145;
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_8);
x_156 = lean_ctor_get(x_146, 1);
lean_inc(x_156);
lean_dec(x_146);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_147);
lean_ctor_set(x_157, 1, x_12);
x_99 = x_157;
x_100 = x_156;
goto block_145;
}
block_145:
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
x_102 = lean_unbox(x_101);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_4);
lean_dec(x_2);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
lean_dec(x_99);
x_104 = l_Lean_getPPAnalysisSkip___closed__4;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_27);
x_105 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_104, x_27, x_14, x_15, x_16, x_17, x_18, x_100);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_apply_10(x_5, x_106, x_11, x_103, x_27, x_14, x_15, x_16, x_17, x_18, x_107);
return x_108;
}
else
{
if (x_7 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_99, 1);
lean_inc(x_109);
lean_dec(x_99);
x_110 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_mvarName(x_2, x_15, x_16, x_17, x_18, x_100);
lean_dec(x_2);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_27);
x_113 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg(x_111, x_11, x_109, x_27, x_14, x_15, x_16, x_17, x_18, x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_117 = !lean_is_exclusive(x_115);
if (x_117 == 0)
{
lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_ctor_get(x_115, 3);
x_119 = 1;
x_120 = lean_box(x_119);
x_121 = lean_array_set(x_118, x_4, x_120);
lean_dec(x_4);
lean_ctor_set(x_115, 3, x_121);
x_122 = lean_box(0);
x_123 = lean_apply_10(x_5, x_122, x_11, x_115, x_27, x_14, x_15, x_16, x_17, x_18, x_116);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_124 = lean_ctor_get(x_115, 0);
x_125 = lean_ctor_get(x_115, 1);
x_126 = lean_ctor_get(x_115, 2);
x_127 = lean_ctor_get(x_115, 3);
x_128 = lean_ctor_get(x_115, 4);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_115);
x_129 = 1;
x_130 = lean_box(x_129);
x_131 = lean_array_set(x_127, x_4, x_130);
lean_dec(x_4);
x_132 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_132, 0, x_124);
lean_ctor_set(x_132, 1, x_125);
lean_ctor_set(x_132, 2, x_126);
lean_ctor_set(x_132, 3, x_131);
lean_ctor_set(x_132, 4, x_128);
x_133 = lean_box(0);
x_134 = lean_apply_10(x_5, x_133, x_11, x_132, x_27, x_14, x_15, x_16, x_17, x_18, x_116);
return x_134;
}
}
else
{
uint8_t x_135; 
lean_dec(x_109);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_135 = !lean_is_exclusive(x_110);
if (x_135 == 0)
{
return x_110;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_110, 0);
x_137 = lean_ctor_get(x_110, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_110);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_4);
lean_dec(x_2);
x_139 = lean_ctor_get(x_99, 1);
lean_inc(x_139);
lean_dec(x_99);
x_140 = l_Lean_getPPAnalysisSkip___closed__4;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_27);
x_141 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_140, x_27, x_14, x_15, x_16, x_17, x_18, x_100);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_apply_10(x_5, x_142, x_11, x_139, x_27, x_14, x_15, x_16, x_17, x_18, x_143);
return x_144;
}
}
}
}
case 2:
{
lean_object* x_158; lean_object* x_159; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_inc(x_2);
x_205 = l___private_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_0__Lean_PrettyPrinter_Delaborator_TopDownAnalyze_valUnknown(x_2, x_15, x_16, x_17, x_18, x_19);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_unbox(x_206);
if (x_207 == 0)
{
lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_206);
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_208);
lean_dec(x_205);
x_209 = l_instInhabitedBool;
x_210 = lean_box(x_209);
x_211 = lean_array_get(x_210, x_8, x_4);
lean_dec(x_8);
x_212 = lean_unbox(x_211);
lean_dec(x_211);
x_213 = lean_box(x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_12);
x_158 = x_214;
x_159 = x_208;
goto block_204;
}
else
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_8);
x_215 = lean_ctor_get(x_205, 1);
lean_inc(x_215);
lean_dec(x_205);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_206);
lean_ctor_set(x_216, 1, x_12);
x_158 = x_216;
x_159 = x_215;
goto block_204;
}
block_204:
{
lean_object* x_160; uint8_t x_161; 
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
x_161 = lean_unbox(x_160);
lean_dec(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_4);
lean_dec(x_2);
x_162 = lean_ctor_get(x_158, 1);
lean_inc(x_162);
lean_dec(x_158);
x_163 = l_Lean_getPPAnalysisSkip___closed__4;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_27);
x_164 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_163, x_27, x_14, x_15, x_16, x_17, x_18, x_159);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_apply_10(x_5, x_165, x_11, x_162, x_27, x_14, x_15, x_16, x_17, x_18, x_166);
return x_167;
}
else
{
if (x_7 == 0)
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_158, 1);
lean_inc(x_168);
lean_dec(x_158);
x_169 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_mvarName(x_2, x_15, x_16, x_17, x_18, x_159);
lean_dec(x_2);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_27);
x_172 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_annotateNamedArg(x_170, x_11, x_168, x_27, x_14, x_15, x_16, x_17, x_18, x_171);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_dec(x_172);
x_176 = !lean_is_exclusive(x_174);
if (x_176 == 0)
{
lean_object* x_177; uint8_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_174, 3);
x_178 = 1;
x_179 = lean_box(x_178);
x_180 = lean_array_set(x_177, x_4, x_179);
lean_dec(x_4);
lean_ctor_set(x_174, 3, x_180);
x_181 = lean_box(0);
x_182 = lean_apply_10(x_5, x_181, x_11, x_174, x_27, x_14, x_15, x_16, x_17, x_18, x_175);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_183 = lean_ctor_get(x_174, 0);
x_184 = lean_ctor_get(x_174, 1);
x_185 = lean_ctor_get(x_174, 2);
x_186 = lean_ctor_get(x_174, 3);
x_187 = lean_ctor_get(x_174, 4);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_174);
x_188 = 1;
x_189 = lean_box(x_188);
x_190 = lean_array_set(x_186, x_4, x_189);
lean_dec(x_4);
x_191 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_191, 0, x_183);
lean_ctor_set(x_191, 1, x_184);
lean_ctor_set(x_191, 2, x_185);
lean_ctor_set(x_191, 3, x_190);
lean_ctor_set(x_191, 4, x_187);
x_192 = lean_box(0);
x_193 = lean_apply_10(x_5, x_192, x_11, x_191, x_27, x_14, x_15, x_16, x_17, x_18, x_175);
return x_193;
}
}
else
{
uint8_t x_194; 
lean_dec(x_168);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
x_194 = !lean_is_exclusive(x_169);
if (x_194 == 0)
{
return x_169;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_169, 0);
x_196 = lean_ctor_get(x_169, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_169);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_4);
lean_dec(x_2);
x_198 = lean_ctor_get(x_158, 1);
lean_inc(x_198);
lean_dec(x_158);
x_199 = l_Lean_getPPAnalysisSkip___closed__4;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_27);
x_200 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_199, x_27, x_14, x_15, x_16, x_17, x_18, x_159);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = lean_apply_10(x_5, x_201, x_11, x_198, x_27, x_14, x_15, x_16, x_17, x_18, x_202);
return x_203;
}
}
}
}
case 3:
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; 
lean_dec(x_8);
lean_dec(x_6);
x_217 = lean_ctor_get(x_17, 2);
lean_inc(x_217);
lean_inc(x_5);
lean_inc(x_4);
x_218 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__3___boxed), 13, 2);
lean_closure_set(x_218, 0, x_4);
lean_closure_set(x_218, 1, x_5);
x_219 = l_Lean_getPPInstances(x_217);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_220 = l_Lean_getPPAnalysisSkip___closed__4;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_27);
x_221 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_220, x_27, x_14, x_15, x_16, x_17, x_18, x_19);
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
lean_dec(x_221);
x_223 = 0;
x_224 = lean_box(0);
x_225 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__3(x_4, x_5, x_223, x_224, x_11, x_12, x_27, x_14, x_15, x_16, x_17, x_18, x_222);
lean_dec(x_4);
return x_225;
}
else
{
uint8_t x_226; 
x_226 = l_Lean_getPPAnalyzeCheckInstances(x_217);
lean_dec(x_217);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_218);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_227 = l_Lean_getPPAnalysisSkip___closed__4;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_27);
x_228 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBool(x_227, x_27, x_14, x_15, x_16, x_17, x_18, x_19);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
lean_dec(x_228);
x_230 = 0;
x_231 = lean_box(0);
x_232 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__3(x_4, x_5, x_230, x_231, x_11, x_12, x_27, x_14, x_15, x_16, x_17, x_18, x_229);
lean_dec(x_4);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; 
lean_dec(x_5);
lean_dec(x_4);
x_233 = lean_box(0);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_234 = l_Lean_Meta_trySynthInstance(x_9, x_233, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = 1;
x_238 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__4(x_2, x_218, x_3, x_237, x_235, x_11, x_12, x_27, x_14, x_15, x_16, x_17, x_18, x_236);
lean_dec(x_2);
return x_238;
}
else
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; 
x_239 = lean_ctor_get(x_234, 1);
lean_inc(x_239);
lean_dec(x_234);
x_240 = lean_box(2);
x_241 = 1;
x_242 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__4(x_2, x_218, x_3, x_241, x_240, x_11, x_12, x_27, x_14, x_15, x_16, x_17, x_18, x_239);
lean_dec(x_2);
return x_242;
}
}
}
}
default: 
{
lean_object* x_243; lean_object* x_244; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_243 = lean_box(0);
x_244 = lean_apply_10(x_5, x_243, x_11, x_12, x_27, x_14, x_15, x_16, x_17, x_18, x_19);
return x_244;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 4);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
x_19 = l_Lean_instInhabitedExpr;
x_20 = lean_array_get(x_19, x_12, x_1);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_20);
x_21 = lean_infer_type(x_20, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_get(x_19, x_13, x_1);
lean_dec(x_13);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Expr_getAppNumArgsAux(x_11, x_25);
lean_dec(x_11);
x_27 = lean_nat_add(x_26, x_1);
lean_dec(x_26);
lean_inc(x_1);
lean_inc(x_20);
lean_inc(x_24);
x_28 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__2), 13, 3);
lean_closure_set(x_28, 0, x_24);
lean_closure_set(x_28, 1, x_20);
lean_closure_set(x_28, 2, x_1);
x_29 = l_Lean_instInhabitedBinderInfo;
x_30 = lean_box(x_29);
x_31 = lean_array_get(x_30, x_14, x_1);
lean_dec(x_14);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
x_33 = lean_box(x_32);
x_34 = lean_box(x_15);
x_35 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__5___boxed), 19, 10);
lean_closure_set(x_35, 0, x_33);
lean_closure_set(x_35, 1, x_24);
lean_closure_set(x_35, 2, x_20);
lean_closure_set(x_35, 3, x_1);
lean_closure_set(x_35, 4, x_28);
lean_closure_set(x_35, 5, x_18);
lean_closure_set(x_35, 6, x_34);
lean_closure_set(x_35, 7, x_17);
lean_closure_set(x_35, 8, x_22);
lean_closure_set(x_35, 9, x_16);
x_36 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___spec__1(x_27, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
lean_dec(x_27);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_21);
if (x_37 == 0)
{
return x_21;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_21, 0);
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_21);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeFn___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___lambda__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___spec__3___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___lambda__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5___boxed(lean_object** _args) {
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
x_18 = l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__3(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__4(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__5___boxed(lean_object** _args) {
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
uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_unbox(x_1);
lean_dec(x_1);
x_21 = lean_unbox(x_7);
lean_dec(x_7);
x_22 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_analyzeArg___lambda__5(x_20, x_2, x_3, x_4, x_5, x_6, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_PrettyPrinter_Delaborator_topDownAnalyze___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_PrettyPrinter_Delaborator_topDownAnalyze___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at_Lean_PrettyPrinter_Delaborator_topDownAnalyze___spec__1___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___boxed), 8, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("error", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_2 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_550; lean_object* x_551; lean_object* x_552; uint8_t x_553; 
x_16 = lean_st_ref_get(x_5, x_6);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_3, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_550 = lean_st_ref_get(x_5, x_20);
x_551 = lean_ctor_get(x_550, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_551, 3);
lean_inc(x_552);
lean_dec(x_551);
x_553 = lean_ctor_get_uint8(x_552, sizeof(void*)*1);
lean_dec(x_552);
if (x_553 == 0)
{
lean_object* x_554; uint8_t x_555; 
x_554 = lean_ctor_get(x_550, 1);
lean_inc(x_554);
lean_dec(x_550);
x_555 = 0;
x_21 = x_555;
x_22 = x_554;
goto block_549;
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; uint8_t x_561; 
x_556 = lean_ctor_get(x_550, 1);
lean_inc(x_556);
lean_dec(x_550);
x_557 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_558 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_557, x_2, x_3, x_4, x_5, x_556);
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_558, 1);
lean_inc(x_560);
lean_dec(x_558);
x_561 = lean_unbox(x_559);
lean_dec(x_559);
x_21 = x_561;
x_22 = x_560;
goto block_549;
}
block_15:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
block_549:
{
if (x_21 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_st_ref_get(x_5, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get_uint8(x_25, sizeof(void*)*1);
lean_dec(x_25);
x_28 = lean_st_ref_take(x_5, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 3);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_86; lean_object* x_95; uint8_t x_109; 
x_35 = 0;
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_35);
x_36 = lean_st_ref_set(x_5, x_29, x_31);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_109 = !lean_is_exclusive(x_2);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_110 = lean_ctor_get(x_2, 0);
x_111 = l_Lean_Elab_Term_setElabConfig(x_110);
lean_ctor_set(x_2, 0, x_111);
x_112 = lean_ctor_get(x_4, 2);
lean_inc(x_112);
x_113 = l_Lean_getPPAnalyzeKnowsType(x_112);
lean_dec(x_112);
x_114 = l_Lean_SubExpr_Pos_root;
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_1);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_113);
lean_ctor_set_uint8(x_116, sizeof(void*)*1 + 1, x_113);
lean_ctor_set_uint8(x_116, sizeof(void*)*1 + 2, x_35);
lean_ctor_set_uint8(x_116, sizeof(void*)*1 + 3, x_35);
x_117 = lean_box(0);
x_118 = lean_st_ref_get(x_5, x_37);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_120 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__2;
x_121 = lean_st_mk_ref(x_120, x_119);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_122);
x_125 = l_Lean_Meta_withNewMCtxDepth___at_Lean_PrettyPrinter_Delaborator_topDownAnalyze___spec__1___rarg(x_124, x_116, x_122, x_2, x_3, x_4, x_5, x_123);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_2);
lean_dec(x_4);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_st_ref_get(x_5, x_126);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_st_ref_get(x_122, x_128);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_st_ref_get(x_5, x_131);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_st_ref_get(x_122, x_134);
lean_dec(x_122);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_135, 0);
lean_dec(x_137);
lean_ctor_set(x_135, 0, x_132);
x_95 = x_135;
goto block_108;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_132);
lean_ctor_set(x_139, 1, x_138);
x_95 = x_139;
goto block_108;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_122);
x_140 = lean_ctor_get(x_125, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_141 = x_125;
} else {
 lean_dec_ref(x_125);
 x_141 = lean_box(0);
}
x_142 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__4;
x_153 = lean_st_ref_get(x_5, x_140);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_154, 3);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_ctor_get_uint8(x_155, sizeof(void*)*1);
lean_dec(x_155);
if (x_156 == 0)
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
lean_dec(x_153);
x_143 = x_35;
x_144 = x_157;
goto block_152;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_158 = lean_ctor_get(x_153, 1);
lean_inc(x_158);
lean_dec(x_153);
x_159 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_142, x_2, x_3, x_4, x_5, x_158);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_unbox(x_160);
lean_dec(x_160);
x_143 = x_162;
x_144 = x_161;
goto block_152;
}
block_152:
{
if (x_143 == 0)
{
lean_object* x_145; 
lean_dec(x_2);
lean_dec(x_4);
if (lean_is_scalar(x_141)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_141;
 lean_ctor_set_tag(x_145, 0);
}
lean_ctor_set(x_145, 0, x_117);
lean_ctor_set(x_145, 1, x_144);
x_95 = x_145;
goto block_108;
}
else
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_141);
x_146 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__6;
x_147 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_142, x_146, x_2, x_3, x_4, x_5, x_144);
lean_dec(x_4);
lean_dec(x_2);
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_147, 0);
lean_dec(x_149);
lean_ctor_set(x_147, 0, x_117);
x_95 = x_147;
goto block_108;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_117);
lean_ctor_set(x_151, 1, x_150);
x_95 = x_151;
goto block_108;
}
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_163 = lean_ctor_get(x_2, 0);
x_164 = lean_ctor_get(x_2, 1);
x_165 = lean_ctor_get(x_2, 2);
x_166 = lean_ctor_get(x_2, 3);
x_167 = lean_ctor_get(x_2, 4);
x_168 = lean_ctor_get(x_2, 5);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_2);
x_169 = l_Lean_Elab_Term_setElabConfig(x_163);
x_170 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_164);
lean_ctor_set(x_170, 2, x_165);
lean_ctor_set(x_170, 3, x_166);
lean_ctor_set(x_170, 4, x_167);
lean_ctor_set(x_170, 5, x_168);
x_171 = lean_ctor_get(x_4, 2);
lean_inc(x_171);
x_172 = l_Lean_getPPAnalyzeKnowsType(x_171);
lean_dec(x_171);
x_173 = l_Lean_SubExpr_Pos_root;
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_1);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set_uint8(x_175, sizeof(void*)*1, x_172);
lean_ctor_set_uint8(x_175, sizeof(void*)*1 + 1, x_172);
lean_ctor_set_uint8(x_175, sizeof(void*)*1 + 2, x_35);
lean_ctor_set_uint8(x_175, sizeof(void*)*1 + 3, x_35);
x_176 = lean_box(0);
x_177 = lean_st_ref_get(x_5, x_37);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
x_179 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__2;
x_180 = lean_st_mk_ref(x_179, x_178);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_170);
lean_inc(x_181);
x_184 = l_Lean_Meta_withNewMCtxDepth___at_Lean_PrettyPrinter_Delaborator_topDownAnalyze___spec__1___rarg(x_183, x_175, x_181, x_170, x_3, x_4, x_5, x_182);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_170);
lean_dec(x_4);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
lean_dec(x_184);
x_186 = lean_st_ref_get(x_5, x_185);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec(x_186);
x_188 = lean_st_ref_get(x_181, x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_ctor_get(x_189, 0);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_st_ref_get(x_5, x_190);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
x_194 = lean_st_ref_get(x_181, x_193);
lean_dec(x_181);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_196 = x_194;
} else {
 lean_dec_ref(x_194);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_191);
lean_ctor_set(x_197, 1, x_195);
x_95 = x_197;
goto block_108;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
lean_dec(x_181);
x_198 = lean_ctor_get(x_184, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_199 = x_184;
} else {
 lean_dec_ref(x_184);
 x_199 = lean_box(0);
}
x_200 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__4;
x_210 = lean_st_ref_get(x_5, x_198);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_211, 3);
lean_inc(x_212);
lean_dec(x_211);
x_213 = lean_ctor_get_uint8(x_212, sizeof(void*)*1);
lean_dec(x_212);
if (x_213 == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_210, 1);
lean_inc(x_214);
lean_dec(x_210);
x_201 = x_35;
x_202 = x_214;
goto block_209;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_215 = lean_ctor_get(x_210, 1);
lean_inc(x_215);
lean_dec(x_210);
x_216 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_200, x_170, x_3, x_4, x_5, x_215);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_unbox(x_217);
lean_dec(x_217);
x_201 = x_219;
x_202 = x_218;
goto block_209;
}
block_209:
{
if (x_201 == 0)
{
lean_object* x_203; 
lean_dec(x_170);
lean_dec(x_4);
if (lean_is_scalar(x_199)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_199;
 lean_ctor_set_tag(x_203, 0);
}
lean_ctor_set(x_203, 0, x_176);
lean_ctor_set(x_203, 1, x_202);
x_95 = x_203;
goto block_108;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_199);
x_204 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__6;
x_205 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_200, x_204, x_170, x_3, x_4, x_5, x_202);
lean_dec(x_4);
lean_dec(x_170);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_207 = x_205;
} else {
 lean_dec_ref(x_205);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_176);
lean_ctor_set(x_208, 1, x_206);
x_95 = x_208;
goto block_108;
}
}
}
}
block_85:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_st_ref_get(x_5, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 3);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get_uint8(x_44, sizeof(void*)*1);
lean_dec(x_44);
x_46 = lean_st_ref_take(x_5, x_43);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_47, 3);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_27);
x_53 = lean_st_ref_set(x_5, x_47, x_49);
lean_dec(x_5);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
x_56 = lean_box(x_45);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_39);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_53, 0, x_57);
x_7 = x_53;
goto block_15;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_box(x_45);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_39);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
x_7 = x_61;
goto block_15;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_48, 0);
lean_inc(x_62);
lean_dec(x_48);
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_27);
lean_ctor_set(x_47, 3, x_63);
x_64 = lean_st_ref_set(x_5, x_47, x_49);
lean_dec(x_5);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_box(x_45);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_39);
lean_ctor_set(x_68, 1, x_67);
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_66;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
x_7 = x_69;
goto block_15;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_70 = lean_ctor_get(x_47, 0);
x_71 = lean_ctor_get(x_47, 1);
x_72 = lean_ctor_get(x_47, 2);
x_73 = lean_ctor_get(x_47, 4);
x_74 = lean_ctor_get(x_47, 5);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_47);
x_75 = lean_ctor_get(x_48, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_76 = x_48;
} else {
 lean_dec_ref(x_48);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 1, 1);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_27);
x_78 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set(x_78, 1, x_71);
lean_ctor_set(x_78, 2, x_72);
lean_ctor_set(x_78, 3, x_77);
lean_ctor_set(x_78, 4, x_73);
lean_ctor_set(x_78, 5, x_74);
x_79 = lean_st_ref_set(x_5, x_78, x_49);
lean_dec(x_5);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = lean_box(x_45);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_39);
lean_ctor_set(x_83, 1, x_82);
if (lean_is_scalar(x_81)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_81;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
x_7 = x_84;
goto block_15;
}
}
block_94:
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec(x_88);
lean_ctor_set(x_86, 0, x_89);
x_38 = x_86;
goto block_85;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_86, 0);
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_86);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_38 = x_93;
goto block_85;
}
}
block_108:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_st_ref_get(x_5, x_97);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_st_ref_set(x_3, x_19, x_99);
lean_dec(x_3);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_96);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_100, 0, x_103);
x_86 = x_100;
goto block_94;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_100, 0);
x_105 = lean_ctor_get(x_100, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_100);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_96);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_86 = x_107;
goto block_94;
}
}
}
else
{
lean_object* x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_254; lean_object* x_261; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_220 = lean_ctor_get(x_30, 0);
lean_inc(x_220);
lean_dec(x_30);
x_221 = 0;
x_222 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set_uint8(x_222, sizeof(void*)*1, x_221);
lean_ctor_set(x_29, 3, x_222);
x_223 = lean_st_ref_set(x_5, x_29, x_31);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
lean_dec(x_223);
x_273 = lean_ctor_get(x_2, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_2, 1);
lean_inc(x_274);
x_275 = lean_ctor_get(x_2, 2);
lean_inc(x_275);
x_276 = lean_ctor_get(x_2, 3);
lean_inc(x_276);
x_277 = lean_ctor_get(x_2, 4);
lean_inc(x_277);
x_278 = lean_ctor_get(x_2, 5);
lean_inc(x_278);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_279 = x_2;
} else {
 lean_dec_ref(x_2);
 x_279 = lean_box(0);
}
x_280 = l_Lean_Elab_Term_setElabConfig(x_273);
if (lean_is_scalar(x_279)) {
 x_281 = lean_alloc_ctor(0, 6, 0);
} else {
 x_281 = x_279;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_274);
lean_ctor_set(x_281, 2, x_275);
lean_ctor_set(x_281, 3, x_276);
lean_ctor_set(x_281, 4, x_277);
lean_ctor_set(x_281, 5, x_278);
x_282 = lean_ctor_get(x_4, 2);
lean_inc(x_282);
x_283 = l_Lean_getPPAnalyzeKnowsType(x_282);
lean_dec(x_282);
x_284 = l_Lean_SubExpr_Pos_root;
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_1);
lean_ctor_set(x_285, 1, x_284);
x_286 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set_uint8(x_286, sizeof(void*)*1, x_283);
lean_ctor_set_uint8(x_286, sizeof(void*)*1 + 1, x_283);
lean_ctor_set_uint8(x_286, sizeof(void*)*1 + 2, x_221);
lean_ctor_set_uint8(x_286, sizeof(void*)*1 + 3, x_221);
x_287 = lean_box(0);
x_288 = lean_st_ref_get(x_5, x_224);
x_289 = lean_ctor_get(x_288, 1);
lean_inc(x_289);
lean_dec(x_288);
x_290 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__2;
x_291 = lean_st_mk_ref(x_290, x_289);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
x_294 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_281);
lean_inc(x_292);
x_295 = l_Lean_Meta_withNewMCtxDepth___at_Lean_PrettyPrinter_Delaborator_topDownAnalyze___spec__1___rarg(x_294, x_286, x_292, x_281, x_3, x_4, x_5, x_293);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_281);
lean_dec(x_4);
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
lean_dec(x_295);
x_297 = lean_st_ref_get(x_5, x_296);
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
lean_dec(x_297);
x_299 = lean_st_ref_get(x_292, x_298);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_ctor_get(x_300, 0);
lean_inc(x_302);
lean_dec(x_300);
x_303 = lean_st_ref_get(x_5, x_301);
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
lean_dec(x_303);
x_305 = lean_st_ref_get(x_292, x_304);
lean_dec(x_292);
x_306 = lean_ctor_get(x_305, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_307 = x_305;
} else {
 lean_dec_ref(x_305);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_302);
lean_ctor_set(x_308, 1, x_306);
x_261 = x_308;
goto block_272;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; lean_object* x_313; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
lean_dec(x_292);
x_309 = lean_ctor_get(x_295, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_310 = x_295;
} else {
 lean_dec_ref(x_295);
 x_310 = lean_box(0);
}
x_311 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__4;
x_321 = lean_st_ref_get(x_5, x_309);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_322, 3);
lean_inc(x_323);
lean_dec(x_322);
x_324 = lean_ctor_get_uint8(x_323, sizeof(void*)*1);
lean_dec(x_323);
if (x_324 == 0)
{
lean_object* x_325; 
x_325 = lean_ctor_get(x_321, 1);
lean_inc(x_325);
lean_dec(x_321);
x_312 = x_221;
x_313 = x_325;
goto block_320;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_326 = lean_ctor_get(x_321, 1);
lean_inc(x_326);
lean_dec(x_321);
x_327 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_311, x_281, x_3, x_4, x_5, x_326);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
x_330 = lean_unbox(x_328);
lean_dec(x_328);
x_312 = x_330;
x_313 = x_329;
goto block_320;
}
block_320:
{
if (x_312 == 0)
{
lean_object* x_314; 
lean_dec(x_281);
lean_dec(x_4);
if (lean_is_scalar(x_310)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_310;
 lean_ctor_set_tag(x_314, 0);
}
lean_ctor_set(x_314, 0, x_287);
lean_ctor_set(x_314, 1, x_313);
x_261 = x_314;
goto block_272;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_310);
x_315 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__6;
x_316 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_311, x_315, x_281, x_3, x_4, x_5, x_313);
lean_dec(x_4);
lean_dec(x_281);
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_318 = x_316;
} else {
 lean_dec_ref(x_316);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_287);
lean_ctor_set(x_319, 1, x_317);
x_261 = x_319;
goto block_272;
}
}
}
block_253:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = lean_st_ref_get(x_5, x_227);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = lean_ctor_get(x_229, 3);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_ctor_get_uint8(x_231, sizeof(void*)*1);
lean_dec(x_231);
x_233 = lean_st_ref_take(x_5, x_230);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_234, 3);
lean_inc(x_235);
x_236 = lean_ctor_get(x_233, 1);
lean_inc(x_236);
lean_dec(x_233);
x_237 = lean_ctor_get(x_234, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_234, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_234, 2);
lean_inc(x_239);
x_240 = lean_ctor_get(x_234, 4);
lean_inc(x_240);
x_241 = lean_ctor_get(x_234, 5);
lean_inc(x_241);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 lean_ctor_release(x_234, 4);
 lean_ctor_release(x_234, 5);
 x_242 = x_234;
} else {
 lean_dec_ref(x_234);
 x_242 = lean_box(0);
}
x_243 = lean_ctor_get(x_235, 0);
lean_inc(x_243);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 x_244 = x_235;
} else {
 lean_dec_ref(x_235);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(0, 1, 1);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set_uint8(x_245, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_242)) {
 x_246 = lean_alloc_ctor(0, 6, 0);
} else {
 x_246 = x_242;
}
lean_ctor_set(x_246, 0, x_237);
lean_ctor_set(x_246, 1, x_238);
lean_ctor_set(x_246, 2, x_239);
lean_ctor_set(x_246, 3, x_245);
lean_ctor_set(x_246, 4, x_240);
lean_ctor_set(x_246, 5, x_241);
x_247 = lean_st_ref_set(x_5, x_246, x_236);
lean_dec(x_5);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_249 = x_247;
} else {
 lean_dec_ref(x_247);
 x_249 = lean_box(0);
}
x_250 = lean_box(x_232);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_226);
lean_ctor_set(x_251, 1, x_250);
if (lean_is_scalar(x_249)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_249;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_248);
x_7 = x_252;
goto block_15;
}
block_260:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_257 = x_254;
} else {
 lean_dec_ref(x_254);
 x_257 = lean_box(0);
}
x_258 = lean_ctor_get(x_255, 0);
lean_inc(x_258);
lean_dec(x_255);
if (lean_is_scalar(x_257)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_257;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_256);
x_225 = x_259;
goto block_253;
}
block_272:
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_st_ref_get(x_5, x_263);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
lean_dec(x_264);
x_266 = lean_st_ref_set(x_3, x_19, x_265);
lean_dec(x_3);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_269 = x_266;
} else {
 lean_dec_ref(x_266);
 x_269 = lean_box(0);
}
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_262);
lean_ctor_set(x_270, 1, x_267);
if (lean_is_scalar(x_269)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_269;
}
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_268);
x_254 = x_271;
goto block_260;
}
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_372; lean_object* x_379; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_331 = lean_ctor_get(x_29, 0);
x_332 = lean_ctor_get(x_29, 1);
x_333 = lean_ctor_get(x_29, 2);
x_334 = lean_ctor_get(x_29, 4);
x_335 = lean_ctor_get(x_29, 5);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_29);
x_336 = lean_ctor_get(x_30, 0);
lean_inc(x_336);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_337 = x_30;
} else {
 lean_dec_ref(x_30);
 x_337 = lean_box(0);
}
x_338 = 0;
if (lean_is_scalar(x_337)) {
 x_339 = lean_alloc_ctor(0, 1, 1);
} else {
 x_339 = x_337;
}
lean_ctor_set(x_339, 0, x_336);
lean_ctor_set_uint8(x_339, sizeof(void*)*1, x_338);
x_340 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_340, 0, x_331);
lean_ctor_set(x_340, 1, x_332);
lean_ctor_set(x_340, 2, x_333);
lean_ctor_set(x_340, 3, x_339);
lean_ctor_set(x_340, 4, x_334);
lean_ctor_set(x_340, 5, x_335);
x_341 = lean_st_ref_set(x_5, x_340, x_31);
x_342 = lean_ctor_get(x_341, 1);
lean_inc(x_342);
lean_dec(x_341);
x_391 = lean_ctor_get(x_2, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_2, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_2, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_2, 3);
lean_inc(x_394);
x_395 = lean_ctor_get(x_2, 4);
lean_inc(x_395);
x_396 = lean_ctor_get(x_2, 5);
lean_inc(x_396);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_397 = x_2;
} else {
 lean_dec_ref(x_2);
 x_397 = lean_box(0);
}
x_398 = l_Lean_Elab_Term_setElabConfig(x_391);
if (lean_is_scalar(x_397)) {
 x_399 = lean_alloc_ctor(0, 6, 0);
} else {
 x_399 = x_397;
}
lean_ctor_set(x_399, 0, x_398);
lean_ctor_set(x_399, 1, x_392);
lean_ctor_set(x_399, 2, x_393);
lean_ctor_set(x_399, 3, x_394);
lean_ctor_set(x_399, 4, x_395);
lean_ctor_set(x_399, 5, x_396);
x_400 = lean_ctor_get(x_4, 2);
lean_inc(x_400);
x_401 = l_Lean_getPPAnalyzeKnowsType(x_400);
lean_dec(x_400);
x_402 = l_Lean_SubExpr_Pos_root;
x_403 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_403, 0, x_1);
lean_ctor_set(x_403, 1, x_402);
x_404 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set_uint8(x_404, sizeof(void*)*1, x_401);
lean_ctor_set_uint8(x_404, sizeof(void*)*1 + 1, x_401);
lean_ctor_set_uint8(x_404, sizeof(void*)*1 + 2, x_338);
lean_ctor_set_uint8(x_404, sizeof(void*)*1 + 3, x_338);
x_405 = lean_box(0);
x_406 = lean_st_ref_get(x_5, x_342);
x_407 = lean_ctor_get(x_406, 1);
lean_inc(x_407);
lean_dec(x_406);
x_408 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__2;
x_409 = lean_st_mk_ref(x_408, x_407);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
x_412 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_399);
lean_inc(x_410);
x_413 = l_Lean_Meta_withNewMCtxDepth___at_Lean_PrettyPrinter_Delaborator_topDownAnalyze___spec__1___rarg(x_412, x_404, x_410, x_399, x_3, x_4, x_5, x_411);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_399);
lean_dec(x_4);
x_414 = lean_ctor_get(x_413, 1);
lean_inc(x_414);
lean_dec(x_413);
x_415 = lean_st_ref_get(x_5, x_414);
x_416 = lean_ctor_get(x_415, 1);
lean_inc(x_416);
lean_dec(x_415);
x_417 = lean_st_ref_get(x_410, x_416);
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
x_420 = lean_ctor_get(x_418, 0);
lean_inc(x_420);
lean_dec(x_418);
x_421 = lean_st_ref_get(x_5, x_419);
x_422 = lean_ctor_get(x_421, 1);
lean_inc(x_422);
lean_dec(x_421);
x_423 = lean_st_ref_get(x_410, x_422);
lean_dec(x_410);
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_425 = x_423;
} else {
 lean_dec_ref(x_423);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(0, 2, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_420);
lean_ctor_set(x_426, 1, x_424);
x_379 = x_426;
goto block_390;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; uint8_t x_430; lean_object* x_431; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; 
lean_dec(x_410);
x_427 = lean_ctor_get(x_413, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 x_428 = x_413;
} else {
 lean_dec_ref(x_413);
 x_428 = lean_box(0);
}
x_429 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__4;
x_439 = lean_st_ref_get(x_5, x_427);
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_440, 3);
lean_inc(x_441);
lean_dec(x_440);
x_442 = lean_ctor_get_uint8(x_441, sizeof(void*)*1);
lean_dec(x_441);
if (x_442 == 0)
{
lean_object* x_443; 
x_443 = lean_ctor_get(x_439, 1);
lean_inc(x_443);
lean_dec(x_439);
x_430 = x_338;
x_431 = x_443;
goto block_438;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; uint8_t x_448; 
x_444 = lean_ctor_get(x_439, 1);
lean_inc(x_444);
lean_dec(x_439);
x_445 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_429, x_399, x_3, x_4, x_5, x_444);
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
lean_dec(x_445);
x_448 = lean_unbox(x_446);
lean_dec(x_446);
x_430 = x_448;
x_431 = x_447;
goto block_438;
}
block_438:
{
if (x_430 == 0)
{
lean_object* x_432; 
lean_dec(x_399);
lean_dec(x_4);
if (lean_is_scalar(x_428)) {
 x_432 = lean_alloc_ctor(0, 2, 0);
} else {
 x_432 = x_428;
 lean_ctor_set_tag(x_432, 0);
}
lean_ctor_set(x_432, 0, x_405);
lean_ctor_set(x_432, 1, x_431);
x_379 = x_432;
goto block_390;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_428);
x_433 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__6;
x_434 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_429, x_433, x_399, x_3, x_4, x_5, x_431);
lean_dec(x_4);
lean_dec(x_399);
x_435 = lean_ctor_get(x_434, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 x_436 = x_434;
} else {
 lean_dec_ref(x_434);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(0, 2, 0);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_405);
lean_ctor_set(x_437, 1, x_435);
x_379 = x_437;
goto block_390;
}
}
}
block_371:
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
x_346 = lean_st_ref_get(x_5, x_345);
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
x_349 = lean_ctor_get(x_347, 3);
lean_inc(x_349);
lean_dec(x_347);
x_350 = lean_ctor_get_uint8(x_349, sizeof(void*)*1);
lean_dec(x_349);
x_351 = lean_st_ref_take(x_5, x_348);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_352, 3);
lean_inc(x_353);
x_354 = lean_ctor_get(x_351, 1);
lean_inc(x_354);
lean_dec(x_351);
x_355 = lean_ctor_get(x_352, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_352, 1);
lean_inc(x_356);
x_357 = lean_ctor_get(x_352, 2);
lean_inc(x_357);
x_358 = lean_ctor_get(x_352, 4);
lean_inc(x_358);
x_359 = lean_ctor_get(x_352, 5);
lean_inc(x_359);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 lean_ctor_release(x_352, 2);
 lean_ctor_release(x_352, 3);
 lean_ctor_release(x_352, 4);
 lean_ctor_release(x_352, 5);
 x_360 = x_352;
} else {
 lean_dec_ref(x_352);
 x_360 = lean_box(0);
}
x_361 = lean_ctor_get(x_353, 0);
lean_inc(x_361);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 x_362 = x_353;
} else {
 lean_dec_ref(x_353);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(0, 1, 1);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set_uint8(x_363, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_360)) {
 x_364 = lean_alloc_ctor(0, 6, 0);
} else {
 x_364 = x_360;
}
lean_ctor_set(x_364, 0, x_355);
lean_ctor_set(x_364, 1, x_356);
lean_ctor_set(x_364, 2, x_357);
lean_ctor_set(x_364, 3, x_363);
lean_ctor_set(x_364, 4, x_358);
lean_ctor_set(x_364, 5, x_359);
x_365 = lean_st_ref_set(x_5, x_364, x_354);
lean_dec(x_5);
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_367 = x_365;
} else {
 lean_dec_ref(x_365);
 x_367 = lean_box(0);
}
x_368 = lean_box(x_350);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_344);
lean_ctor_set(x_369, 1, x_368);
if (lean_is_scalar(x_367)) {
 x_370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_370 = x_367;
}
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_366);
x_7 = x_370;
goto block_15;
}
block_378:
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_372, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_375 = x_372;
} else {
 lean_dec_ref(x_372);
 x_375 = lean_box(0);
}
x_376 = lean_ctor_get(x_373, 0);
lean_inc(x_376);
lean_dec(x_373);
if (lean_is_scalar(x_375)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_375;
}
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_374);
x_343 = x_377;
goto block_371;
}
block_390:
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
lean_dec(x_379);
x_382 = lean_st_ref_get(x_5, x_381);
x_383 = lean_ctor_get(x_382, 1);
lean_inc(x_383);
lean_dec(x_382);
x_384 = lean_st_ref_set(x_3, x_19, x_383);
lean_dec(x_3);
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_387 = x_384;
} else {
 lean_dec_ref(x_384);
 x_387 = lean_box(0);
}
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_380);
lean_ctor_set(x_388, 1, x_385);
if (lean_is_scalar(x_387)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_387;
}
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_386);
x_372 = x_389;
goto block_378;
}
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_466; lean_object* x_475; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; uint8_t x_498; lean_object* x_499; lean_object* x_500; uint8_t x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_449 = lean_ctor_get(x_4, 5);
lean_inc(x_449);
x_450 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__7___rarg(x_5, x_22);
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
lean_dec(x_450);
x_489 = lean_ctor_get(x_2, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_2, 1);
lean_inc(x_490);
x_491 = lean_ctor_get(x_2, 2);
lean_inc(x_491);
x_492 = lean_ctor_get(x_2, 3);
lean_inc(x_492);
x_493 = lean_ctor_get(x_2, 4);
lean_inc(x_493);
x_494 = lean_ctor_get(x_2, 5);
lean_inc(x_494);
x_495 = l_Lean_Elab_Term_setElabConfig(x_489);
x_496 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_496, 0, x_495);
lean_ctor_set(x_496, 1, x_490);
lean_ctor_set(x_496, 2, x_491);
lean_ctor_set(x_496, 3, x_492);
lean_ctor_set(x_496, 4, x_493);
lean_ctor_set(x_496, 5, x_494);
x_497 = lean_ctor_get(x_4, 2);
lean_inc(x_497);
x_498 = l_Lean_getPPAnalyzeKnowsType(x_497);
lean_dec(x_497);
x_499 = l_Lean_SubExpr_Pos_root;
x_500 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_500, 0, x_1);
lean_ctor_set(x_500, 1, x_499);
x_501 = 0;
x_502 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set_uint8(x_502, sizeof(void*)*1, x_498);
lean_ctor_set_uint8(x_502, sizeof(void*)*1 + 1, x_498);
lean_ctor_set_uint8(x_502, sizeof(void*)*1 + 2, x_501);
lean_ctor_set_uint8(x_502, sizeof(void*)*1 + 3, x_501);
x_503 = lean_box(0);
x_504 = lean_st_ref_get(x_5, x_452);
x_505 = lean_ctor_get(x_504, 1);
lean_inc(x_505);
lean_dec(x_504);
x_506 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__2;
x_507 = lean_st_mk_ref(x_506, x_505);
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_507, 1);
lean_inc(x_509);
lean_dec(x_507);
x_510 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_496);
lean_inc(x_508);
x_511 = l_Lean_Meta_withNewMCtxDepth___at_Lean_PrettyPrinter_Delaborator_topDownAnalyze___spec__1___rarg(x_510, x_502, x_508, x_496, x_3, x_4, x_5, x_509);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; 
lean_dec(x_496);
x_512 = lean_ctor_get(x_511, 1);
lean_inc(x_512);
lean_dec(x_511);
x_513 = lean_st_ref_get(x_5, x_512);
x_514 = lean_ctor_get(x_513, 1);
lean_inc(x_514);
lean_dec(x_513);
x_515 = lean_st_ref_get(x_508, x_514);
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_515, 1);
lean_inc(x_517);
lean_dec(x_515);
x_518 = lean_ctor_get(x_516, 0);
lean_inc(x_518);
lean_dec(x_516);
x_519 = lean_st_ref_get(x_5, x_517);
x_520 = lean_ctor_get(x_519, 1);
lean_inc(x_520);
lean_dec(x_519);
x_521 = lean_st_ref_get(x_508, x_520);
lean_dec(x_508);
x_522 = !lean_is_exclusive(x_521);
if (x_522 == 0)
{
lean_object* x_523; 
x_523 = lean_ctor_get(x_521, 0);
lean_dec(x_523);
lean_ctor_set(x_521, 0, x_518);
x_475 = x_521;
goto block_488;
}
else
{
lean_object* x_524; lean_object* x_525; 
x_524 = lean_ctor_get(x_521, 1);
lean_inc(x_524);
lean_dec(x_521);
x_525 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_525, 0, x_518);
lean_ctor_set(x_525, 1, x_524);
x_475 = x_525;
goto block_488;
}
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; uint8_t x_529; lean_object* x_530; lean_object* x_539; lean_object* x_540; lean_object* x_541; uint8_t x_542; 
lean_dec(x_508);
x_526 = lean_ctor_get(x_511, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_527 = x_511;
} else {
 lean_dec_ref(x_511);
 x_527 = lean_box(0);
}
x_528 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__4;
x_539 = lean_st_ref_get(x_5, x_526);
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_540, 3);
lean_inc(x_541);
lean_dec(x_540);
x_542 = lean_ctor_get_uint8(x_541, sizeof(void*)*1);
lean_dec(x_541);
if (x_542 == 0)
{
lean_object* x_543; 
x_543 = lean_ctor_get(x_539, 1);
lean_inc(x_543);
lean_dec(x_539);
x_529 = x_501;
x_530 = x_543;
goto block_538;
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; uint8_t x_548; 
x_544 = lean_ctor_get(x_539, 1);
lean_inc(x_544);
lean_dec(x_539);
x_545 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_528, x_496, x_3, x_4, x_5, x_544);
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_545, 1);
lean_inc(x_547);
lean_dec(x_545);
x_548 = lean_unbox(x_546);
lean_dec(x_546);
x_529 = x_548;
x_530 = x_547;
goto block_538;
}
block_538:
{
if (x_529 == 0)
{
lean_object* x_531; 
lean_dec(x_496);
if (lean_is_scalar(x_527)) {
 x_531 = lean_alloc_ctor(0, 2, 0);
} else {
 x_531 = x_527;
 lean_ctor_set_tag(x_531, 0);
}
lean_ctor_set(x_531, 0, x_503);
lean_ctor_set(x_531, 1, x_530);
x_475 = x_531;
goto block_488;
}
else
{
lean_object* x_532; lean_object* x_533; uint8_t x_534; 
lean_dec(x_527);
x_532 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__6;
x_533 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_528, x_532, x_496, x_3, x_4, x_5, x_530);
lean_dec(x_496);
x_534 = !lean_is_exclusive(x_533);
if (x_534 == 0)
{
lean_object* x_535; 
x_535 = lean_ctor_get(x_533, 0);
lean_dec(x_535);
lean_ctor_set(x_533, 0, x_503);
x_475 = x_533;
goto block_488;
}
else
{
lean_object* x_536; lean_object* x_537; 
x_536 = lean_ctor_get(x_533, 1);
lean_inc(x_536);
lean_dec(x_533);
x_537 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_537, 0, x_503);
lean_ctor_set(x_537, 1, x_536);
x_475 = x_537;
goto block_488;
}
}
}
}
block_465:
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; 
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
lean_dec(x_453);
x_456 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_457 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_451, x_456, x_449, x_2, x_3, x_4, x_5, x_455);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_458 = !lean_is_exclusive(x_457);
if (x_458 == 0)
{
lean_object* x_459; lean_object* x_460; 
x_459 = lean_ctor_get(x_457, 0);
x_460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_460, 0, x_454);
lean_ctor_set(x_460, 1, x_459);
lean_ctor_set(x_457, 0, x_460);
x_7 = x_457;
goto block_15;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_461 = lean_ctor_get(x_457, 0);
x_462 = lean_ctor_get(x_457, 1);
lean_inc(x_462);
lean_inc(x_461);
lean_dec(x_457);
x_463 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_463, 0, x_454);
lean_ctor_set(x_463, 1, x_461);
x_464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_462);
x_7 = x_464;
goto block_15;
}
}
block_474:
{
uint8_t x_467; 
x_467 = !lean_is_exclusive(x_466);
if (x_467 == 0)
{
lean_object* x_468; lean_object* x_469; 
x_468 = lean_ctor_get(x_466, 0);
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
lean_dec(x_468);
lean_ctor_set(x_466, 0, x_469);
x_453 = x_466;
goto block_465;
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_470 = lean_ctor_get(x_466, 0);
x_471 = lean_ctor_get(x_466, 1);
lean_inc(x_471);
lean_inc(x_470);
lean_dec(x_466);
x_472 = lean_ctor_get(x_470, 0);
lean_inc(x_472);
lean_dec(x_470);
x_473 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_471);
x_453 = x_473;
goto block_465;
}
}
block_488:
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_475, 1);
lean_inc(x_477);
lean_dec(x_475);
x_478 = lean_st_ref_get(x_5, x_477);
x_479 = lean_ctor_get(x_478, 1);
lean_inc(x_479);
lean_dec(x_478);
x_480 = lean_st_ref_set(x_3, x_19, x_479);
x_481 = !lean_is_exclusive(x_480);
if (x_481 == 0)
{
lean_object* x_482; lean_object* x_483; 
x_482 = lean_ctor_get(x_480, 0);
x_483 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_483, 0, x_476);
lean_ctor_set(x_483, 1, x_482);
lean_ctor_set(x_480, 0, x_483);
x_466 = x_480;
goto block_474;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_484 = lean_ctor_get(x_480, 0);
x_485 = lean_ctor_get(x_480, 1);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_480);
x_486 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_486, 0, x_476);
lean_ctor_set(x_486, 1, x_484);
x_487 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_485);
x_466 = x_487;
goto block_474;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_9562____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tryUnify", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_9562____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_2 = l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_9562____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_9562_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__2;
x_6 = l_Lean_registerTraceClass(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_9562____closed__2;
x_9 = l_Lean_registerTraceClass(x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__4;
x_12 = l_Lean_registerTraceClass(x_11, x_10);
return x_12;
}
else
{
uint8_t x_13; 
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
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
return x_6;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_RBMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FindMVar(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FindLevelMVar(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_ReplaceLevel(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Delaborator_Options(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Delaborator_SubExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Config(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrettyPrinter_Delaborator_TopDownAnalyze(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_RBMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindMVar(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindLevelMVar(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceLevel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Delaborator_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Delaborator_SubExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__4);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__5 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__5);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__6 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__6);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__7 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__7();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10____closed__7);
if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_10_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze);
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38____closed__4);
if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_38_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_checkInstances = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_checkInstances);
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66____closed__4);
if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_66_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_typeAscriptions = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_typeAscriptions);
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94____closed__4);
if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_94_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_trustSubst = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_trustSubst);
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122____closed__4);
if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_122_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_trustOfNat = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_trustOfNat);
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150____closed__4);
if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_150_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_trustOfScientific = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_trustOfScientific);
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178____closed__4);
if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_178_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_trustCoe = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_trustCoe);
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206____closed__4);
if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_206_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_trustSubtypeMk = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_trustSubtypeMk);
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234____closed__4);
if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_234_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_trustId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_trustId);
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262____closed__4);
if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_262_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_trustKnownFOType2TypeHOFuns = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_trustKnownFOType2TypeHOFuns);
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290____closed__4);
if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_290_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_omitMax = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_omitMax);
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318____closed__4);
if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_318_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_knowsType = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_knowsType);
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346____closed__4);
if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_346_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_analyze_explicitHoles = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_analyze_explicitHoles);
lean_dec_ref(res);
}l_Lean_getPPAnalysisSkip___closed__1 = _init_l_Lean_getPPAnalysisSkip___closed__1();
lean_mark_persistent(l_Lean_getPPAnalysisSkip___closed__1);
l_Lean_getPPAnalysisSkip___closed__2 = _init_l_Lean_getPPAnalysisSkip___closed__2();
lean_mark_persistent(l_Lean_getPPAnalysisSkip___closed__2);
l_Lean_getPPAnalysisSkip___closed__3 = _init_l_Lean_getPPAnalysisSkip___closed__3();
lean_mark_persistent(l_Lean_getPPAnalysisSkip___closed__3);
l_Lean_getPPAnalysisSkip___closed__4 = _init_l_Lean_getPPAnalysisSkip___closed__4();
lean_mark_persistent(l_Lean_getPPAnalysisSkip___closed__4);
l_Lean_getPPAnalysisHole___closed__1 = _init_l_Lean_getPPAnalysisHole___closed__1();
lean_mark_persistent(l_Lean_getPPAnalysisHole___closed__1);
l_Lean_getPPAnalysisHole___closed__2 = _init_l_Lean_getPPAnalysisHole___closed__2();
lean_mark_persistent(l_Lean_getPPAnalysisHole___closed__2);
l_Lean_getPPAnalysisNamedArg___closed__1 = _init_l_Lean_getPPAnalysisNamedArg___closed__1();
lean_mark_persistent(l_Lean_getPPAnalysisNamedArg___closed__1);
l_Lean_getPPAnalysisNamedArg___closed__2 = _init_l_Lean_getPPAnalysisNamedArg___closed__2();
lean_mark_persistent(l_Lean_getPPAnalysisNamedArg___closed__2);
l_Lean_getPPAnalysisLetVarType___closed__1 = _init_l_Lean_getPPAnalysisLetVarType___closed__1();
lean_mark_persistent(l_Lean_getPPAnalysisLetVarType___closed__1);
l_Lean_getPPAnalysisLetVarType___closed__2 = _init_l_Lean_getPPAnalysisLetVarType___closed__2();
lean_mark_persistent(l_Lean_getPPAnalysisLetVarType___closed__2);
l_Lean_getPPAnalysisNeedsType___closed__1 = _init_l_Lean_getPPAnalysisNeedsType___closed__1();
lean_mark_persistent(l_Lean_getPPAnalysisNeedsType___closed__1);
l_Lean_getPPAnalysisNeedsType___closed__2 = _init_l_Lean_getPPAnalysisNeedsType___closed__2();
lean_mark_persistent(l_Lean_getPPAnalysisNeedsType___closed__2);
l_Lean_getPPAnalysisBlockImplicit___closed__1 = _init_l_Lean_getPPAnalysisBlockImplicit___closed__1();
lean_mark_persistent(l_Lean_getPPAnalysisBlockImplicit___closed__1);
l_Lean_getPPAnalysisBlockImplicit___closed__2 = _init_l_Lean_getPPAnalysisBlockImplicit___closed__2();
lean_mark_persistent(l_Lean_getPPAnalysisBlockImplicit___closed__2);
l_Lean_PrettyPrinter_Delaborator_returnsPi___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_returnsPi___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_returnsPi___closed__1);
l_Lean_PrettyPrinter_Delaborator_isCoe___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_isCoe___closed__1);
l_Lean_PrettyPrinter_Delaborator_isCoe___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_isCoe___closed__2);
l_Lean_PrettyPrinter_Delaborator_isCoe___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_isCoe___closed__3);
l_Lean_PrettyPrinter_Delaborator_isCoe___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_isCoe___closed__4);
l_Lean_PrettyPrinter_Delaborator_isCoe___closed__5 = _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_isCoe___closed__5);
l_Lean_PrettyPrinter_Delaborator_isCoe___closed__6 = _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_isCoe___closed__6);
l_Lean_PrettyPrinter_Delaborator_isCoe___closed__7 = _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_isCoe___closed__7);
l_Lean_PrettyPrinter_Delaborator_isCoe___closed__8 = _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_isCoe___closed__8);
l_Lean_PrettyPrinter_Delaborator_isCoe___closed__9 = _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_isCoe___closed__9);
l_Lean_PrettyPrinter_Delaborator_isCoe___closed__10 = _init_l_Lean_PrettyPrinter_Delaborator_isCoe___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_isCoe___closed__10);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__2);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__3);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__4);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__5 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__5);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__6 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__6);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__7 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__7);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__8 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__8);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__9 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__9);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__10 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__10);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__11 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__11);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__12 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__12);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__13 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__13();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__13);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__14 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__14();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__14);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__15 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__15();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__15);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__16 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__16();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__16);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__17 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__17();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__17);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__18 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__18();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__18);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__19 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__19();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__19);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__20 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__20();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__20);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__21 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__21();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__21);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__22 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__22();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__22);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__23 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__23();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__23);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__24 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__24();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__24);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__25 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__25();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__25);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__26 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__26();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__26);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__27 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__27();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__27);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__28 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__28();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__28);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__29 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__29();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__29);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__30 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__30();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__30);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__31 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__31();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__31);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__32 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__32();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__32);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__33 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__33();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__33);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__34 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__34();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__34);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__35 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__35();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__35);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__36 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__36();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__36);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__37 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__37();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__37);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__38 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__38();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__38);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__39 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__39();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__39);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__40 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__40();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__40);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__41 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__41();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__41);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__42 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__42();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__42);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__43 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__43();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__43);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__44 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__44();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__44);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__45 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__45();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__45);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__46 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__46();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__46);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__47 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__47();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__47);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__48 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__48();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__48);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__49 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__49();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__49);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__50 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__50();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__50);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__51 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__51();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__51);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__52 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__52();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__52);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__53 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__53();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__53);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__54 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__54();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__54);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__55 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__55();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__55);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__56 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__56();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__56);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__57 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__57();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__57);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__58 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__58();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__58);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__59 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__59();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__59);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__60 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__60();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__60);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__61 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__61();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__61);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__62 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__62();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__62);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__63 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__63();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__63);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__64 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__64();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__64);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__65 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__65();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__65);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__66 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__66();
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__67 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__67();
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__68 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHBinOp___lambda__1___closed__68();
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__2);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__3);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__1___closed__4);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__2);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_replaceLPsWithVars___lambda__2___closed__3);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isHigherOrder___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isFunLike___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__2);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__3);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__4);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__5 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__5);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__6 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isSubstLike___closed__6);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_Context_inBottomUp___default = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_Context_inBottomUp___default();
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_Context_parentIsApp___default = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_Context_parentIsApp___default();
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__1();
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__2);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__3);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext___closed__4);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instInhabitedContext);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_State_annotations___default = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_State_annotations___default();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_State_annotations___default);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_State_postponed___default = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_State_postponed___default();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_State_postponed___default);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM___closed__2);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_instMonadReaderOfSubExprAnalyzeM);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_tryUnify___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_inspectOutParams___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__2);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__3);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__4);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__5 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__5);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__6 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__6);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__7 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__7);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__8 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_isTrivialBottomUp___closed__8);
l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_canBottomUp___spec__1___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_3187____closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_3187____closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_3187____closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_3187____closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_3187____closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_3187____closed__2);
if (builtin) {res = l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_3187_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeFailureId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeFailureId);
lean_dec_ref(res);
}l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_checkKnowsType___closed__2);
l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__1 = _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__1);
l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__2 = _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__2);
l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__3 = _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__3);
l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__4 = _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__4();
lean_mark_persistent(l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__4);
l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__5 = _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__5();
lean_mark_persistent(l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__5);
l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__6 = _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__6();
lean_mark_persistent(l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__6);
l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__7 = _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__7();
lean_mark_persistent(l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__7);
l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__8 = _init_l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__8();
lean_mark_persistent(l_Lean_addTrace___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__3___closed__8);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__2);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__3);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___closed__4);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_App_State_namedArgs___default = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_App_State_namedArgs___default();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_App_State_namedArgs___default);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_collectBottomUps___closed__1);
l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__1);
l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__2);
l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__3 = _init_l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_applyFunBinderHeuristic_core___spec__2___closed__3);
l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1___closed__1 = _init_l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1___closed__1);
l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1___closed__2 = _init_l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1___closed__2);
l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1___closed__3 = _init_l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___spec__1___closed__3);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__2);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__3);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__4);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__5 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__5);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__6 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__6);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__7 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeConst___closed__7);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__2);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__3);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__4);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__5 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__5);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__6 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__6);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__7 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__7);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__8 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__8);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__9 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze___closed__9);
l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1 = _init_l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1();
lean_mark_persistent(l_panic___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__2___closed__1);
l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__1);
l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__2);
l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__1___closed__3);
l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__1);
l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__14___closed__2);
l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__1);
l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___spec__27___closed__2);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___closed__2);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLet___closed__3);
l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__1);
l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeMData___spec__1___closed__2);
l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__1);
l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeProj___spec__1___closed__2);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeLam___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__2);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__3);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__4);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__5 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeApp___closed__5);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__2);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__3);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyze_analyzeAppStaged___lambda__1___closed__4);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___closed__1);
l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_analyzeAppStagedCore_maybeSetExplicit___closed__2);
l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__1);
l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__2);
l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__3);
l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__4);
l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__5 = _init_l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__5);
l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__6 = _init_l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_topDownAnalyze___closed__6);
l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_9562____closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_9562____closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_9562____closed__1);
l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_9562____closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_9562____closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_9562____closed__2);
res = l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_TopDownAnalyze___hyg_9562_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
