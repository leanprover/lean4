// Lean compiler output
// Module: Lean.Compiler.LCNF.ToLCNF
// Imports: Lean.ProjFns Lean.Meta.CtorRecognizer Lean.Compiler.BorrowedAnnotation Lean.Compiler.CSimpAttr Lean.Compiler.ImplementedByAttr Lean.Compiler.LCNF.Types Lean.Compiler.LCNF.Bind Lean.Compiler.LCNF.InferType Lean.Compiler.LCNF.Util
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
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__3;
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__2;
lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_litToValue(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13;
lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__3;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__1;
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__5;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7;
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__25;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__1;
lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__21;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__14;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__4;
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__14;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__9;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__0;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__4;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__3;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at___Lean_Compiler_SpecState_addEntry_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__2;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_isLCProof(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__1;
lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__1;
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__4;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda___closed__0;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__27;
uint8_t l_Lean_Expr_isLambda(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__3;
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__8;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getCtorArity_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__2;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__8;
lean_object* l_Lean_Compiler_LCNF_joinTypes(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__0;
uint8_t l_Lean_Compiler_LCNF_isPredicateType(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__20;
lean_object* l_instMonadEIO(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17;
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__0;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___closed__0;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__5;
uint8_t lean_is_marked_borrowed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_csimp_replace_constants(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__2;
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___closed__0;
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__18;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__5;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9;
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t lean_is_no_confusion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5;
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__23;
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_erase___at___Lean_LocalContext_erase_spec__1___redArg(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2;
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__6;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__1___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__3;
lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12;
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__13;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4;
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__0;
lean_object* l_Lean_Compiler_LCNF_CasesInfo_numAlts(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__0;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__10;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isRuntimeBultinType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6;
uint8_t l_Lean_BinderInfo_isImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__10;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3;
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(lean_object*, lean_object*);
lean_object* l_Lean_Expr_toCtorIfLit(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__19;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__4;
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9;
static lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__16;
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__4;
lean_object* l_Lean_Compiler_LCNF_getCasesInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5;
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__0;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__0;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkParam(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__26;
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__24;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__7;
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1;
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
static uint64_t l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__3;
lean_object* l_Lean_Expr_letFunAppArgs_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__9;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__5;
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Compiler_LCNF_anyExpr;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Param_toExpr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1;
lean_object* l_Lean_Compiler_LCNF_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__5;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__7;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8;
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__1;
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_get_projection_info(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__6;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__16;
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__2;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__0;
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(lean_object*);
static lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__1;
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lcProof", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_isLCProof(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1;
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__0;
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__0;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__4;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__3;
x_3 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__0;
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__6;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(x_1, x_2, x_6);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
if (lean_obj_tag(x_13) == 4)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_array_get_size(x_18);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_dec(x_17);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
else
{
lean_free_object(x_7);
x_1 = x_17;
x_3 = x_15;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_dec(x_7);
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_array_get_size(x_25);
lean_dec(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_24);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
else
{
x_1 = x_24;
x_3 = x_23;
goto _start;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_13);
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_7, 0);
lean_dec(x_32);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
lean_dec(x_7);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_16 = x_5;
} else {
 lean_dec_ref(x_5);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_19 = x_13;
} else {
 lean_dec_ref(x_13);
 x_19 = lean_box(0);
}
x_20 = lean_array_uget(x_14, x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 2);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_22, x_18, x_1, x_10);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = lean_unbox(x_26);
x_28 = l_Lean_Compiler_LCNF_mkAuxParam(x_24, x_27, x_6, x_7, x_8, x_9, x_25);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; size_t x_57; lean_object* x_58; uint8_t x_59; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_array_push(x_17, x_29);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_34);
x_45 = lean_array_get_size(x_33);
x_46 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_21);
x_47 = 32;
x_48 = lean_uint64_shift_right(x_46, x_47);
x_49 = lean_uint64_xor(x_46, x_48);
x_50 = 16;
x_51 = lean_uint64_shift_right(x_49, x_50);
x_52 = lean_uint64_xor(x_49, x_51);
x_53 = lean_uint64_to_usize(x_52);
x_54 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_55 = 1;
x_56 = lean_usize_sub(x_54, x_55);
x_57 = lean_usize_land(x_53, x_56);
x_58 = lean_array_uget(x_33, x_57);
x_59 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_21, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_32, x_60);
lean_dec(x_32);
lean_inc(x_36);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_21);
lean_ctor_set(x_62, 1, x_36);
lean_ctor_set(x_62, 2, x_58);
x_63 = lean_array_uset(x_33, x_57, x_62);
x_64 = lean_unsigned_to_nat(4u);
x_65 = lean_nat_mul(x_61, x_64);
x_66 = lean_unsigned_to_nat(3u);
x_67 = lean_nat_div(x_65, x_66);
lean_dec(x_65);
x_68 = lean_array_get_size(x_63);
x_69 = lean_nat_dec_le(x_67, x_68);
lean_dec(x_68);
lean_dec(x_67);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_63);
lean_ctor_set(x_18, 1, x_70);
lean_ctor_set(x_18, 0, x_61);
x_37 = x_18;
goto block_44;
}
else
{
lean_ctor_set(x_18, 1, x_63);
lean_ctor_set(x_18, 0, x_61);
x_37 = x_18;
goto block_44;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_box(0);
x_72 = lean_array_uset(x_33, x_57, x_71);
lean_inc(x_36);
x_73 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_21, x_36, x_58);
x_74 = lean_array_uset(x_72, x_57, x_73);
lean_ctor_set(x_18, 1, x_74);
x_37 = x_18;
goto block_44;
}
block_44:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; 
x_38 = lean_array_push(x_15, x_36);
if (lean_is_scalar(x_19)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_19;
}
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_37);
if (lean_is_scalar(x_16)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_16;
}
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = 1;
x_42 = lean_usize_add(x_4, x_41);
x_4 = x_42;
x_5 = x_40;
x_10 = x_30;
goto _start;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_88; uint64_t x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; uint64_t x_93; uint64_t x_94; uint64_t x_95; size_t x_96; size_t x_97; size_t x_98; size_t x_99; size_t x_100; lean_object* x_101; uint8_t x_102; 
x_75 = lean_ctor_get(x_18, 0);
x_76 = lean_ctor_get(x_18, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_18);
x_77 = lean_ctor_get(x_29, 0);
lean_inc(x_77);
x_78 = lean_array_push(x_17, x_29);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_77);
x_88 = lean_array_get_size(x_76);
x_89 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_21);
x_90 = 32;
x_91 = lean_uint64_shift_right(x_89, x_90);
x_92 = lean_uint64_xor(x_89, x_91);
x_93 = 16;
x_94 = lean_uint64_shift_right(x_92, x_93);
x_95 = lean_uint64_xor(x_92, x_94);
x_96 = lean_uint64_to_usize(x_95);
x_97 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_98 = 1;
x_99 = lean_usize_sub(x_97, x_98);
x_100 = lean_usize_land(x_96, x_99);
x_101 = lean_array_uget(x_76, x_100);
x_102 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__0___redArg(x_21, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_add(x_75, x_103);
lean_dec(x_75);
lean_inc(x_79);
x_105 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_105, 0, x_21);
lean_ctor_set(x_105, 1, x_79);
lean_ctor_set(x_105, 2, x_101);
x_106 = lean_array_uset(x_76, x_100, x_105);
x_107 = lean_unsigned_to_nat(4u);
x_108 = lean_nat_mul(x_104, x_107);
x_109 = lean_unsigned_to_nat(3u);
x_110 = lean_nat_div(x_108, x_109);
lean_dec(x_108);
x_111 = lean_array_get_size(x_106);
x_112 = lean_nat_dec_le(x_110, x_111);
lean_dec(x_111);
lean_dec(x_110);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectType_spec__1___redArg(x_106);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_104);
lean_ctor_set(x_114, 1, x_113);
x_80 = x_114;
goto block_87;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_104);
lean_ctor_set(x_115, 1, x_106);
x_80 = x_115;
goto block_87;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_box(0);
x_117 = lean_array_uset(x_76, x_100, x_116);
lean_inc(x_79);
x_118 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0___redArg(x_21, x_79, x_101);
x_119 = lean_array_uset(x_117, x_100, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_75);
lean_ctor_set(x_120, 1, x_119);
x_80 = x_120;
goto block_87;
}
block_87:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; size_t x_84; size_t x_85; 
x_81 = lean_array_push(x_15, x_79);
if (lean_is_scalar(x_19)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_19;
}
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_80);
if (lean_is_scalar(x_16)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_16;
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = 1;
x_85 = lean_usize_add(x_4, x_84);
x_4 = x_85;
x_5 = x_83;
x_10 = x_30;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_1, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_uget(x_4, x_3);
x_14 = lean_box(0);
x_15 = lean_array_uset(x_4, x_3, x_14);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
x_26 = lean_ctor_get(x_13, 2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_26, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_ctor_set(x_13, 2, x_28);
x_16 = x_13;
x_17 = x_29;
goto block_22;
}
else
{
uint8_t x_30; 
lean_free_object(x_13);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get(x_13, 1);
x_36 = lean_ctor_get(x_13, 2);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_37 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_36, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_38);
x_16 = x_40;
x_17 = x_39;
goto block_22;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_43 = x_37;
} else {
 lean_dec_ref(x_37);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_13);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_13, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_46, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_ctor_set(x_13, 0, x_48);
x_16 = x_13;
x_17 = x_49;
goto block_22;
}
else
{
uint8_t x_50; 
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 0);
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_47);
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
x_54 = lean_ctor_get(x_13, 0);
lean_inc(x_54);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_55 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_54, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_56);
x_16 = x_58;
x_17 = x_57;
goto block_22;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_61 = x_55;
} else {
 lean_dec_ref(x_55);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
block_22:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_20 = lean_array_uset(x_15, x_3, x_16);
x_3 = x_19;
x_4 = x_20;
x_10 = x_17;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__6;
x_2 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__5;
x_3 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__4;
x_4 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__3;
x_5 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__2;
x_6 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_5);
lean_ctor_set(x_8, 5, x_4);
lean_ctor_set(x_8, 6, x_3);
lean_ctor_set(x_8, 7, x_2);
lean_ctor_set(x_8, 8, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 5);
x_8 = lean_st_ref_get(x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_st_ref_get(x_2, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_dec(x_18);
x_19 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec(x_17);
x_20 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__7;
lean_inc(x_6);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_19);
lean_ctor_set(x_21, 3, x_6);
lean_ctor_set_tag(x_14, 3);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 0, x_21);
lean_inc(x_7);
lean_ctor_set(x_8, 1, x_14);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_8);
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_22);
lean_dec(x_22);
x_24 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__7;
lean_inc(x_6);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_6);
x_26 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_1);
lean_inc(x_7);
lean_ctor_set(x_8, 1, x_26);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_8);
return x_12;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_31 = x_27;
} else {
 lean_dec_ref(x_27);
 x_31 = lean_box(0);
}
x_32 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_30);
lean_dec(x_30);
x_33 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__7;
lean_inc(x_6);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_6);
if (lean_is_scalar(x_31)) {
 x_35 = lean_alloc_ctor(3, 2, 0);
} else {
 x_35 = x_31;
 lean_ctor_set_tag(x_35, 3);
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_1);
lean_inc(x_7);
lean_ctor_set(x_8, 1, x_35);
lean_ctor_set(x_8, 0, x_7);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_8);
lean_ctor_set(x_36, 1, x_28);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_37 = lean_ctor_get(x_8, 0);
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_8);
x_39 = lean_st_ref_get(x_2, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_45 = x_40;
} else {
 lean_dec_ref(x_40);
 x_45 = lean_box(0);
}
x_46 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_44);
lean_dec(x_44);
x_47 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__7;
lean_inc(x_6);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_46);
lean_ctor_set(x_48, 3, x_6);
if (lean_is_scalar(x_45)) {
 x_49 = lean_alloc_ctor(3, 2, 0);
} else {
 x_49 = x_45;
 lean_ctor_set_tag(x_49, 3);
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_1);
lean_inc(x_7);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_7);
lean_ctor_set(x_50, 1, x_49);
if (lean_is_scalar(x_42)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_42;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_41);
return x_51;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_alt", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_x", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__10;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_jp", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__13;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`Code.bind` failed, empty `cases` found", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_11 = x_2;
} else {
 lean_dec_ref(x_2);
 x_11 = lean_box(0);
}
if (lean_obj_tag(x_10) == 5)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_10, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_9, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_9, 3);
lean_inc(x_71);
x_72 = lean_name_eq(x_70, x_69);
lean_dec(x_69);
lean_dec(x_70);
if (x_72 == 0)
{
lean_dec(x_71);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
goto block_68;
}
else
{
if (lean_obj_tag(x_71) == 4)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_75 = x_71;
} else {
 lean_dec_ref(x_71);
 x_75 = lean_box(0);
}
lean_inc(x_73);
x_76 = l_Lean_Compiler_LCNF_getBinderName___redArg(x_73, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
if (lean_obj_tag(x_77) == 0)
{
x_79 = x_77;
goto block_414;
}
else
{
lean_object* x_415; 
x_415 = lean_ctor_get(x_77, 0);
lean_inc(x_415);
lean_dec(x_77);
x_79 = x_415;
goto block_414;
}
block_414:
{
lean_object* x_80; uint8_t x_81; 
x_80 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__1;
x_81 = lean_name_eq(x_79, x_80);
lean_dec(x_79);
if (x_81 == 0)
{
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_78;
goto block_68;
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_inc(x_73);
x_82 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___redArg(x_73, x_5, x_78);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_84;
goto block_68;
}
else
{
lean_object* x_85; uint8_t x_86; 
lean_dec(x_11);
lean_dec(x_10);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = !lean_is_exclusive(x_83);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_83, 0);
x_88 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_9, x_5, x_85);
lean_dec(x_9);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_88, 1);
x_91 = lean_ctor_get(x_88, 0);
lean_dec(x_91);
x_92 = lean_st_ref_get(x_3, x_90);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_ctor_get(x_92, 1);
x_96 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_94, x_73);
lean_dec(x_94);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; size_t x_104; size_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_free_object(x_92);
lean_free_object(x_88);
x_97 = lean_ctor_get(x_87, 2);
lean_inc(x_97);
lean_dec(x_87);
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_array_get_size(x_74);
x_100 = l_Array_toSubarray___redArg(x_97, x_98, x_99);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 2);
lean_inc(x_102);
x_103 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9;
x_104 = lean_usize_of_nat(x_102);
lean_dec(x_102);
x_105 = lean_usize_of_nat(x_101);
lean_dec(x_101);
x_106 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_72, x_100, x_104, x_105, x_103, x_4, x_5, x_6, x_7, x_95);
lean_dec(x_100);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
x_110 = !lean_is_exclusive(x_107);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_107, 0);
x_112 = lean_ctor_get(x_107, 1);
lean_dec(x_112);
x_113 = !lean_is_exclusive(x_108);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_108, 0);
x_115 = lean_ctor_get(x_108, 1);
lean_dec(x_115);
lean_inc(x_73);
if (lean_is_scalar(x_75)) {
 x_116 = lean_alloc_ctor(4, 2, 0);
} else {
 x_116 = x_75;
}
lean_ctor_set(x_116, 0, x_73);
lean_ctor_set(x_116, 1, x_111);
x_117 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_118 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_116, x_117, x_4, x_5, x_6, x_7, x_109);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_1, 0);
x_122 = lean_ctor_get(x_119, 0);
lean_inc(x_122);
lean_ctor_set(x_83, 0, x_122);
x_123 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12;
x_124 = lean_array_push(x_123, x_83);
lean_inc(x_121);
lean_ctor_set_tag(x_108, 3);
lean_ctor_set(x_108, 1, x_124);
lean_ctor_set(x_108, 0, x_121);
lean_ctor_set(x_107, 0, x_119);
x_125 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__14;
x_126 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_114, x_107, x_125, x_4, x_5, x_6, x_7, x_120);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_st_ref_take(x_3, x_128);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_131 = lean_ctor_get(x_129, 0);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_127);
x_133 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_131, x_73, x_127);
x_134 = lean_st_ref_set(x_3, x_133, x_132);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_134, 0);
lean_dec(x_136);
x_137 = lean_ctor_get(x_127, 0);
lean_inc(x_137);
lean_dec(x_127);
lean_ctor_set_tag(x_129, 3);
lean_ctor_set(x_129, 1, x_74);
lean_ctor_set(x_129, 0, x_137);
lean_ctor_set(x_134, 0, x_129);
return x_134;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
lean_dec(x_134);
x_139 = lean_ctor_get(x_127, 0);
lean_inc(x_139);
lean_dec(x_127);
lean_ctor_set_tag(x_129, 3);
lean_ctor_set(x_129, 1, x_74);
lean_ctor_set(x_129, 0, x_139);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_129);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_141 = lean_ctor_get(x_129, 0);
x_142 = lean_ctor_get(x_129, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_129);
lean_inc(x_127);
x_143 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_141, x_73, x_127);
x_144 = lean_st_ref_set(x_3, x_143, x_142);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_127, 0);
lean_inc(x_147);
lean_dec(x_127);
x_148 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_74);
if (lean_is_scalar(x_146)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_146;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_145);
return x_149;
}
}
else
{
uint8_t x_150; 
lean_dec(x_74);
lean_dec(x_73);
x_150 = !lean_is_exclusive(x_126);
if (x_150 == 0)
{
return x_126;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_126, 0);
x_152 = lean_ctor_get(x_126, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_126);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; 
lean_free_object(x_108);
lean_dec(x_114);
lean_free_object(x_107);
lean_free_object(x_83);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_154 = !lean_is_exclusive(x_118);
if (x_154 == 0)
{
return x_118;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_118, 0);
x_156 = lean_ctor_get(x_118, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_118);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_108, 0);
lean_inc(x_158);
lean_dec(x_108);
lean_inc(x_73);
if (lean_is_scalar(x_75)) {
 x_159 = lean_alloc_ctor(4, 2, 0);
} else {
 x_159 = x_75;
}
lean_ctor_set(x_159, 0, x_73);
lean_ctor_set(x_159, 1, x_111);
x_160 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_161 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_159, x_160, x_4, x_5, x_6, x_7, x_109);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_ctor_get(x_1, 0);
x_165 = lean_ctor_get(x_162, 0);
lean_inc(x_165);
lean_ctor_set(x_83, 0, x_165);
x_166 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12;
x_167 = lean_array_push(x_166, x_83);
lean_inc(x_164);
x_168 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_168, 0, x_164);
lean_ctor_set(x_168, 1, x_167);
lean_ctor_set(x_107, 1, x_168);
lean_ctor_set(x_107, 0, x_162);
x_169 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__14;
x_170 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_158, x_107, x_169, x_4, x_5, x_6, x_7, x_163);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_st_ref_take(x_3, x_172);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_176 = x_173;
} else {
 lean_dec_ref(x_173);
 x_176 = lean_box(0);
}
lean_inc(x_171);
x_177 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_174, x_73, x_171);
x_178 = lean_st_ref_set(x_3, x_177, x_175);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_180 = x_178;
} else {
 lean_dec_ref(x_178);
 x_180 = lean_box(0);
}
x_181 = lean_ctor_get(x_171, 0);
lean_inc(x_181);
lean_dec(x_171);
if (lean_is_scalar(x_176)) {
 x_182 = lean_alloc_ctor(3, 2, 0);
} else {
 x_182 = x_176;
 lean_ctor_set_tag(x_182, 3);
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_74);
if (lean_is_scalar(x_180)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_180;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_179);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_74);
lean_dec(x_73);
x_184 = lean_ctor_get(x_170, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_170, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_186 = x_170;
} else {
 lean_dec_ref(x_170);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_158);
lean_free_object(x_107);
lean_free_object(x_83);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_188 = lean_ctor_get(x_161, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_161, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_190 = x_161;
} else {
 lean_dec_ref(x_161);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_192 = lean_ctor_get(x_107, 0);
lean_inc(x_192);
lean_dec(x_107);
x_193 = lean_ctor_get(x_108, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_194 = x_108;
} else {
 lean_dec_ref(x_108);
 x_194 = lean_box(0);
}
lean_inc(x_73);
if (lean_is_scalar(x_75)) {
 x_195 = lean_alloc_ctor(4, 2, 0);
} else {
 x_195 = x_75;
}
lean_ctor_set(x_195, 0, x_73);
lean_ctor_set(x_195, 1, x_192);
x_196 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_197 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_195, x_196, x_4, x_5, x_6, x_7, x_109);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_ctor_get(x_1, 0);
x_201 = lean_ctor_get(x_198, 0);
lean_inc(x_201);
lean_ctor_set(x_83, 0, x_201);
x_202 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12;
x_203 = lean_array_push(x_202, x_83);
lean_inc(x_200);
if (lean_is_scalar(x_194)) {
 x_204 = lean_alloc_ctor(3, 2, 0);
} else {
 x_204 = x_194;
 lean_ctor_set_tag(x_204, 3);
}
lean_ctor_set(x_204, 0, x_200);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_198);
lean_ctor_set(x_205, 1, x_204);
x_206 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__14;
x_207 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_193, x_205, x_206, x_4, x_5, x_6, x_7, x_199);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = lean_st_ref_take(x_3, x_209);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_213 = x_210;
} else {
 lean_dec_ref(x_210);
 x_213 = lean_box(0);
}
lean_inc(x_208);
x_214 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_211, x_73, x_208);
x_215 = lean_st_ref_set(x_3, x_214, x_212);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_217 = x_215;
} else {
 lean_dec_ref(x_215);
 x_217 = lean_box(0);
}
x_218 = lean_ctor_get(x_208, 0);
lean_inc(x_218);
lean_dec(x_208);
if (lean_is_scalar(x_213)) {
 x_219 = lean_alloc_ctor(3, 2, 0);
} else {
 x_219 = x_213;
 lean_ctor_set_tag(x_219, 3);
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_74);
if (lean_is_scalar(x_217)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_217;
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_216);
return x_220;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_74);
lean_dec(x_73);
x_221 = lean_ctor_get(x_207, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_207, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_223 = x_207;
} else {
 lean_dec_ref(x_207);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_194);
lean_dec(x_193);
lean_free_object(x_83);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_225 = lean_ctor_get(x_197, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_197, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_227 = x_197;
} else {
 lean_dec_ref(x_197);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
}
else
{
lean_object* x_229; lean_object* x_230; 
lean_free_object(x_83);
lean_dec(x_87);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_229 = lean_ctor_get(x_96, 0);
lean_inc(x_229);
lean_dec(x_96);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
lean_dec(x_229);
lean_ctor_set_tag(x_88, 3);
lean_ctor_set(x_88, 1, x_74);
lean_ctor_set(x_88, 0, x_230);
lean_ctor_set(x_92, 0, x_88);
return x_92;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_92, 0);
x_232 = lean_ctor_get(x_92, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_92);
x_233 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_231, x_73);
lean_dec(x_231);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; size_t x_241; size_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_free_object(x_88);
x_234 = lean_ctor_get(x_87, 2);
lean_inc(x_234);
lean_dec(x_87);
x_235 = lean_unsigned_to_nat(0u);
x_236 = lean_array_get_size(x_74);
x_237 = l_Array_toSubarray___redArg(x_234, x_235, x_236);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 2);
lean_inc(x_239);
x_240 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9;
x_241 = lean_usize_of_nat(x_239);
lean_dec(x_239);
x_242 = lean_usize_of_nat(x_238);
lean_dec(x_238);
x_243 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_72, x_237, x_241, x_242, x_240, x_4, x_5, x_6, x_7, x_232);
lean_dec(x_237);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
x_246 = lean_ctor_get(x_243, 1);
lean_inc(x_246);
lean_dec(x_243);
x_247 = lean_ctor_get(x_244, 0);
lean_inc(x_247);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_248 = x_244;
} else {
 lean_dec_ref(x_244);
 x_248 = lean_box(0);
}
x_249 = lean_ctor_get(x_245, 0);
lean_inc(x_249);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_250 = x_245;
} else {
 lean_dec_ref(x_245);
 x_250 = lean_box(0);
}
lean_inc(x_73);
if (lean_is_scalar(x_75)) {
 x_251 = lean_alloc_ctor(4, 2, 0);
} else {
 x_251 = x_75;
}
lean_ctor_set(x_251, 0, x_73);
lean_ctor_set(x_251, 1, x_247);
x_252 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_253 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_251, x_252, x_4, x_5, x_6, x_7, x_246);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_ctor_get(x_1, 0);
x_257 = lean_ctor_get(x_254, 0);
lean_inc(x_257);
lean_ctor_set(x_83, 0, x_257);
x_258 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12;
x_259 = lean_array_push(x_258, x_83);
lean_inc(x_256);
if (lean_is_scalar(x_250)) {
 x_260 = lean_alloc_ctor(3, 2, 0);
} else {
 x_260 = x_250;
 lean_ctor_set_tag(x_260, 3);
}
lean_ctor_set(x_260, 0, x_256);
lean_ctor_set(x_260, 1, x_259);
if (lean_is_scalar(x_248)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_248;
}
lean_ctor_set(x_261, 0, x_254);
lean_ctor_set(x_261, 1, x_260);
x_262 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__14;
x_263 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_249, x_261, x_262, x_4, x_5, x_6, x_7, x_255);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
x_266 = lean_st_ref_take(x_3, x_265);
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
lean_inc(x_264);
x_270 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_267, x_73, x_264);
x_271 = lean_st_ref_set(x_3, x_270, x_268);
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_273 = x_271;
} else {
 lean_dec_ref(x_271);
 x_273 = lean_box(0);
}
x_274 = lean_ctor_get(x_264, 0);
lean_inc(x_274);
lean_dec(x_264);
if (lean_is_scalar(x_269)) {
 x_275 = lean_alloc_ctor(3, 2, 0);
} else {
 x_275 = x_269;
 lean_ctor_set_tag(x_275, 3);
}
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_74);
if (lean_is_scalar(x_273)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_273;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_272);
return x_276;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_74);
lean_dec(x_73);
x_277 = lean_ctor_get(x_263, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_263, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_279 = x_263;
} else {
 lean_dec_ref(x_263);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_free_object(x_83);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_281 = lean_ctor_get(x_253, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_253, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_283 = x_253;
} else {
 lean_dec_ref(x_253);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_free_object(x_83);
lean_dec(x_87);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_285 = lean_ctor_get(x_233, 0);
lean_inc(x_285);
lean_dec(x_233);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
lean_dec(x_285);
lean_ctor_set_tag(x_88, 3);
lean_ctor_set(x_88, 1, x_74);
lean_ctor_set(x_88, 0, x_286);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_88);
lean_ctor_set(x_287, 1, x_232);
return x_287;
}
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_288 = lean_ctor_get(x_88, 1);
lean_inc(x_288);
lean_dec(x_88);
x_289 = lean_st_ref_get(x_3, x_288);
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_292 = x_289;
} else {
 lean_dec_ref(x_289);
 x_292 = lean_box(0);
}
x_293 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_290, x_73);
lean_dec(x_290);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; size_t x_301; size_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_292);
x_294 = lean_ctor_get(x_87, 2);
lean_inc(x_294);
lean_dec(x_87);
x_295 = lean_unsigned_to_nat(0u);
x_296 = lean_array_get_size(x_74);
x_297 = l_Array_toSubarray___redArg(x_294, x_295, x_296);
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 2);
lean_inc(x_299);
x_300 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9;
x_301 = lean_usize_of_nat(x_299);
lean_dec(x_299);
x_302 = lean_usize_of_nat(x_298);
lean_dec(x_298);
x_303 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_72, x_297, x_301, x_302, x_300, x_4, x_5, x_6, x_7, x_291);
lean_dec(x_297);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
x_306 = lean_ctor_get(x_303, 1);
lean_inc(x_306);
lean_dec(x_303);
x_307 = lean_ctor_get(x_304, 0);
lean_inc(x_307);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_308 = x_304;
} else {
 lean_dec_ref(x_304);
 x_308 = lean_box(0);
}
x_309 = lean_ctor_get(x_305, 0);
lean_inc(x_309);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_310 = x_305;
} else {
 lean_dec_ref(x_305);
 x_310 = lean_box(0);
}
lean_inc(x_73);
if (lean_is_scalar(x_75)) {
 x_311 = lean_alloc_ctor(4, 2, 0);
} else {
 x_311 = x_75;
}
lean_ctor_set(x_311, 0, x_73);
lean_ctor_set(x_311, 1, x_307);
x_312 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_313 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_311, x_312, x_4, x_5, x_6, x_7, x_306);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = lean_ctor_get(x_1, 0);
x_317 = lean_ctor_get(x_314, 0);
lean_inc(x_317);
lean_ctor_set(x_83, 0, x_317);
x_318 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12;
x_319 = lean_array_push(x_318, x_83);
lean_inc(x_316);
if (lean_is_scalar(x_310)) {
 x_320 = lean_alloc_ctor(3, 2, 0);
} else {
 x_320 = x_310;
 lean_ctor_set_tag(x_320, 3);
}
lean_ctor_set(x_320, 0, x_316);
lean_ctor_set(x_320, 1, x_319);
if (lean_is_scalar(x_308)) {
 x_321 = lean_alloc_ctor(0, 2, 0);
} else {
 x_321 = x_308;
}
lean_ctor_set(x_321, 0, x_314);
lean_ctor_set(x_321, 1, x_320);
x_322 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__14;
x_323 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_309, x_321, x_322, x_4, x_5, x_6, x_7, x_315);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_326 = lean_st_ref_take(x_3, x_325);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 x_329 = x_326;
} else {
 lean_dec_ref(x_326);
 x_329 = lean_box(0);
}
lean_inc(x_324);
x_330 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_327, x_73, x_324);
x_331 = lean_st_ref_set(x_3, x_330, x_328);
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_333 = x_331;
} else {
 lean_dec_ref(x_331);
 x_333 = lean_box(0);
}
x_334 = lean_ctor_get(x_324, 0);
lean_inc(x_334);
lean_dec(x_324);
if (lean_is_scalar(x_329)) {
 x_335 = lean_alloc_ctor(3, 2, 0);
} else {
 x_335 = x_329;
 lean_ctor_set_tag(x_335, 3);
}
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_74);
if (lean_is_scalar(x_333)) {
 x_336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_336 = x_333;
}
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_332);
return x_336;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_74);
lean_dec(x_73);
x_337 = lean_ctor_get(x_323, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_323, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_339 = x_323;
} else {
 lean_dec_ref(x_323);
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
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_310);
lean_dec(x_309);
lean_dec(x_308);
lean_free_object(x_83);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_341 = lean_ctor_get(x_313, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_313, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_343 = x_313;
} else {
 lean_dec_ref(x_313);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(1, 2, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_341);
lean_ctor_set(x_344, 1, x_342);
return x_344;
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_free_object(x_83);
lean_dec(x_87);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_345 = lean_ctor_get(x_293, 0);
lean_inc(x_345);
lean_dec(x_293);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
lean_dec(x_345);
x_347 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_74);
if (lean_is_scalar(x_292)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_292;
}
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_291);
return x_348;
}
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_349 = lean_ctor_get(x_83, 0);
lean_inc(x_349);
lean_dec(x_83);
x_350 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_9, x_5, x_85);
lean_dec(x_9);
x_351 = lean_ctor_get(x_350, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_352 = x_350;
} else {
 lean_dec_ref(x_350);
 x_352 = lean_box(0);
}
x_353 = lean_st_ref_get(x_3, x_351);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_356 = x_353;
} else {
 lean_dec_ref(x_353);
 x_356 = lean_box(0);
}
x_357 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_354, x_73);
lean_dec(x_354);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; size_t x_365; size_t x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_356);
lean_dec(x_352);
x_358 = lean_ctor_get(x_349, 2);
lean_inc(x_358);
lean_dec(x_349);
x_359 = lean_unsigned_to_nat(0u);
x_360 = lean_array_get_size(x_74);
x_361 = l_Array_toSubarray___redArg(x_358, x_359, x_360);
x_362 = lean_ctor_get(x_361, 1);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 2);
lean_inc(x_363);
x_364 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9;
x_365 = lean_usize_of_nat(x_363);
lean_dec(x_363);
x_366 = lean_usize_of_nat(x_362);
lean_dec(x_362);
x_367 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_72, x_361, x_365, x_366, x_364, x_4, x_5, x_6, x_7, x_355);
lean_dec(x_361);
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_367, 1);
lean_inc(x_370);
lean_dec(x_367);
x_371 = lean_ctor_get(x_368, 0);
lean_inc(x_371);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_372 = x_368;
} else {
 lean_dec_ref(x_368);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_369, 0);
lean_inc(x_373);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_374 = x_369;
} else {
 lean_dec_ref(x_369);
 x_374 = lean_box(0);
}
lean_inc(x_73);
if (lean_is_scalar(x_75)) {
 x_375 = lean_alloc_ctor(4, 2, 0);
} else {
 x_375 = x_75;
}
lean_ctor_set(x_375, 0, x_73);
lean_ctor_set(x_375, 1, x_371);
x_376 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_377 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_375, x_376, x_4, x_5, x_6, x_7, x_370);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
x_380 = lean_ctor_get(x_1, 0);
x_381 = lean_ctor_get(x_378, 0);
lean_inc(x_381);
x_382 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_382, 0, x_381);
x_383 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12;
x_384 = lean_array_push(x_383, x_382);
lean_inc(x_380);
if (lean_is_scalar(x_374)) {
 x_385 = lean_alloc_ctor(3, 2, 0);
} else {
 x_385 = x_374;
 lean_ctor_set_tag(x_385, 3);
}
lean_ctor_set(x_385, 0, x_380);
lean_ctor_set(x_385, 1, x_384);
if (lean_is_scalar(x_372)) {
 x_386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_386 = x_372;
}
lean_ctor_set(x_386, 0, x_378);
lean_ctor_set(x_386, 1, x_385);
x_387 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__14;
x_388 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_373, x_386, x_387, x_4, x_5, x_6, x_7, x_379);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = lean_st_ref_take(x_3, x_390);
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_394 = x_391;
} else {
 lean_dec_ref(x_391);
 x_394 = lean_box(0);
}
lean_inc(x_389);
x_395 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_392, x_73, x_389);
x_396 = lean_st_ref_set(x_3, x_395, x_393);
x_397 = lean_ctor_get(x_396, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_398 = x_396;
} else {
 lean_dec_ref(x_396);
 x_398 = lean_box(0);
}
x_399 = lean_ctor_get(x_389, 0);
lean_inc(x_399);
lean_dec(x_389);
if (lean_is_scalar(x_394)) {
 x_400 = lean_alloc_ctor(3, 2, 0);
} else {
 x_400 = x_394;
 lean_ctor_set_tag(x_400, 3);
}
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_74);
if (lean_is_scalar(x_398)) {
 x_401 = lean_alloc_ctor(0, 2, 0);
} else {
 x_401 = x_398;
}
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_397);
return x_401;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_74);
lean_dec(x_73);
x_402 = lean_ctor_get(x_388, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_388, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_404 = x_388;
} else {
 lean_dec_ref(x_388);
 x_404 = lean_box(0);
}
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(1, 2, 0);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_402);
lean_ctor_set(x_405, 1, x_403);
return x_405;
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_372);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_406 = lean_ctor_get(x_377, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_377, 1);
lean_inc(x_407);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_408 = x_377;
} else {
 lean_dec_ref(x_377);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 2, 0);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_406);
lean_ctor_set(x_409, 1, x_407);
return x_409;
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_dec(x_349);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_410 = lean_ctor_get(x_357, 0);
lean_inc(x_410);
lean_dec(x_357);
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
lean_dec(x_410);
if (lean_is_scalar(x_352)) {
 x_412 = lean_alloc_ctor(3, 2, 0);
} else {
 x_412 = x_352;
 lean_ctor_set_tag(x_412, 3);
}
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_74);
if (lean_is_scalar(x_356)) {
 x_413 = lean_alloc_ctor(0, 2, 0);
} else {
 x_413 = x_356;
}
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_355);
return x_413;
}
}
}
}
}
}
else
{
uint8_t x_416; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_416 = !lean_is_exclusive(x_76);
if (x_416 == 0)
{
return x_76;
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_417 = lean_ctor_get(x_76, 0);
x_418 = lean_ctor_get(x_76, 1);
lean_inc(x_418);
lean_inc(x_417);
lean_dec(x_76);
x_419 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_418);
return x_419;
}
}
}
else
{
lean_dec(x_71);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
goto block_68;
}
}
}
else
{
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
goto block_68;
}
block_68:
{
lean_object* x_18; 
x_18 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_10, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_12, x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_9, 0);
lean_inc(x_25);
x_26 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_23, x_25);
lean_dec(x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_25);
if (lean_is_scalar(x_11)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_11;
}
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_21, 0, x_27);
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_free_object(x_21);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_take(x_12, x_24);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = l_Lean_RBNode_erase___at___Lean_LocalContext_erase_spec__1___redArg(x_25, x_31);
lean_dec(x_25);
x_34 = lean_st_ref_set(x_12, x_33, x_32);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
if (lean_is_scalar(x_11)) {
 x_37 = lean_alloc_ctor(2, 2, 0);
} else {
 x_37 = x_11;
 lean_ctor_set_tag(x_37, 2);
}
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_19);
lean_ctor_set(x_29, 1, x_37);
lean_ctor_set(x_29, 0, x_9);
lean_ctor_set(x_34, 0, x_29);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
if (lean_is_scalar(x_11)) {
 x_39 = lean_alloc_ctor(2, 2, 0);
} else {
 x_39 = x_11;
 lean_ctor_set_tag(x_39, 2);
}
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_19);
lean_ctor_set(x_29, 1, x_39);
lean_ctor_set(x_29, 0, x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_29, 0);
x_42 = lean_ctor_get(x_29, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_29);
x_43 = l_Lean_RBNode_erase___at___Lean_LocalContext_erase_spec__1___redArg(x_25, x_41);
lean_dec(x_25);
x_44 = lean_st_ref_set(x_12, x_43, x_42);
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
if (lean_is_scalar(x_11)) {
 x_47 = lean_alloc_ctor(2, 2, 0);
} else {
 x_47 = x_11;
 lean_ctor_set_tag(x_47, 2);
}
lean_ctor_set(x_47, 0, x_28);
lean_ctor_set(x_47, 1, x_19);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_9);
lean_ctor_set(x_48, 1, x_47);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_21, 0);
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_21);
x_52 = lean_ctor_get(x_9, 0);
lean_inc(x_52);
x_53 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_50, x_52);
lean_dec(x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_52);
if (lean_is_scalar(x_11)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_11;
}
lean_ctor_set(x_54, 0, x_9);
lean_ctor_set(x_54, 1, x_19);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_st_ref_take(x_12, x_51);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_61 = l_Lean_RBNode_erase___at___Lean_LocalContext_erase_spec__1___redArg(x_52, x_58);
lean_dec(x_52);
x_62 = lean_st_ref_set(x_12, x_61, x_59);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_11)) {
 x_65 = lean_alloc_ctor(2, 2, 0);
} else {
 x_65 = x_11;
 lean_ctor_set_tag(x_65, 2);
}
lean_ctor_set(x_65, 0, x_56);
lean_ctor_set(x_65, 1, x_19);
if (lean_is_scalar(x_60)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_60;
}
lean_ctor_set(x_66, 0, x_9);
lean_ctor_set(x_66, 1, x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
return x_67;
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_9);
return x_18;
}
}
}
case 1:
{
uint8_t x_420; 
x_420 = !lean_is_exclusive(x_2);
if (x_420 == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_421 = lean_ctor_get(x_2, 0);
x_422 = lean_ctor_get(x_2, 1);
x_423 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_422, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_423) == 0)
{
uint8_t x_424; 
x_424 = !lean_is_exclusive(x_423);
if (x_424 == 0)
{
lean_object* x_425; 
x_425 = lean_ctor_get(x_423, 0);
lean_ctor_set(x_2, 1, x_425);
lean_ctor_set(x_423, 0, x_2);
return x_423;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_426 = lean_ctor_get(x_423, 0);
x_427 = lean_ctor_get(x_423, 1);
lean_inc(x_427);
lean_inc(x_426);
lean_dec(x_423);
lean_ctor_set(x_2, 1, x_426);
x_428 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_428, 0, x_2);
lean_ctor_set(x_428, 1, x_427);
return x_428;
}
}
else
{
lean_free_object(x_2);
lean_dec(x_421);
return x_423;
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_429 = lean_ctor_get(x_2, 0);
x_430 = lean_ctor_get(x_2, 1);
lean_inc(x_430);
lean_inc(x_429);
lean_dec(x_2);
x_431 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_430, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_434 = x_431;
} else {
 lean_dec_ref(x_431);
 x_434 = lean_box(0);
}
x_435 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_435, 0, x_429);
lean_ctor_set(x_435, 1, x_432);
if (lean_is_scalar(x_434)) {
 x_436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_436 = x_434;
}
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_433);
return x_436;
}
else
{
lean_dec(x_429);
return x_431;
}
}
}
case 2:
{
uint8_t x_437; 
x_437 = !lean_is_exclusive(x_2);
if (x_437 == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_438 = lean_ctor_get(x_2, 0);
x_439 = lean_ctor_get(x_2, 1);
x_440 = lean_ctor_get(x_438, 2);
lean_inc(x_440);
x_441 = lean_ctor_get(x_438, 4);
lean_inc(x_441);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_442 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_441, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
lean_inc(x_443);
lean_inc(x_440);
x_445 = l_Lean_Compiler_LCNF_Code_inferParamType(x_440, x_443, x_4, x_5, x_6, x_7, x_444);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
lean_dec(x_445);
x_448 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_438, x_446, x_440, x_443, x_5, x_447);
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
lean_dec(x_448);
x_451 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_439, x_3, x_4, x_5, x_6, x_7, x_450);
if (lean_obj_tag(x_451) == 0)
{
uint8_t x_452; 
x_452 = !lean_is_exclusive(x_451);
if (x_452 == 0)
{
lean_object* x_453; 
x_453 = lean_ctor_get(x_451, 0);
lean_ctor_set(x_2, 1, x_453);
lean_ctor_set(x_2, 0, x_449);
lean_ctor_set(x_451, 0, x_2);
return x_451;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_454 = lean_ctor_get(x_451, 0);
x_455 = lean_ctor_get(x_451, 1);
lean_inc(x_455);
lean_inc(x_454);
lean_dec(x_451);
lean_ctor_set(x_2, 1, x_454);
lean_ctor_set(x_2, 0, x_449);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_2);
lean_ctor_set(x_456, 1, x_455);
return x_456;
}
}
else
{
lean_dec(x_449);
lean_free_object(x_2);
return x_451;
}
}
else
{
uint8_t x_457; 
lean_dec(x_443);
lean_dec(x_440);
lean_free_object(x_2);
lean_dec(x_439);
lean_dec(x_438);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_457 = !lean_is_exclusive(x_445);
if (x_457 == 0)
{
return x_445;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_458 = lean_ctor_get(x_445, 0);
x_459 = lean_ctor_get(x_445, 1);
lean_inc(x_459);
lean_inc(x_458);
lean_dec(x_445);
x_460 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_460, 0, x_458);
lean_ctor_set(x_460, 1, x_459);
return x_460;
}
}
}
else
{
lean_dec(x_440);
lean_free_object(x_2);
lean_dec(x_439);
lean_dec(x_438);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_442;
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_461 = lean_ctor_get(x_2, 0);
x_462 = lean_ctor_get(x_2, 1);
lean_inc(x_462);
lean_inc(x_461);
lean_dec(x_2);
x_463 = lean_ctor_get(x_461, 2);
lean_inc(x_463);
x_464 = lean_ctor_get(x_461, 4);
lean_inc(x_464);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_465 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_464, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
lean_dec(x_465);
lean_inc(x_466);
lean_inc(x_463);
x_468 = l_Lean_Compiler_LCNF_Code_inferParamType(x_463, x_466, x_4, x_5, x_6, x_7, x_467);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_468, 1);
lean_inc(x_470);
lean_dec(x_468);
x_471 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_461, x_469, x_463, x_466, x_5, x_470);
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_471, 1);
lean_inc(x_473);
lean_dec(x_471);
x_474 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_462, x_3, x_4, x_5, x_6, x_7, x_473);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_474, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_477 = x_474;
} else {
 lean_dec_ref(x_474);
 x_477 = lean_box(0);
}
x_478 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_478, 0, x_472);
lean_ctor_set(x_478, 1, x_475);
if (lean_is_scalar(x_477)) {
 x_479 = lean_alloc_ctor(0, 2, 0);
} else {
 x_479 = x_477;
}
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_476);
return x_479;
}
else
{
lean_dec(x_472);
return x_474;
}
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
lean_dec(x_466);
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_480 = lean_ctor_get(x_468, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_468, 1);
lean_inc(x_481);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 x_482 = x_468;
} else {
 lean_dec_ref(x_468);
 x_482 = lean_box(0);
}
if (lean_is_scalar(x_482)) {
 x_483 = lean_alloc_ctor(1, 2, 0);
} else {
 x_483 = x_482;
}
lean_ctor_set(x_483, 0, x_480);
lean_ctor_set(x_483, 1, x_481);
return x_483;
}
}
else
{
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_465;
}
}
}
case 4:
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; size_t x_490; size_t x_491; lean_object* x_492; 
x_484 = lean_ctor_get(x_2, 0);
lean_inc(x_484);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_485 = x_2;
} else {
 lean_dec_ref(x_2);
 x_485 = lean_box(0);
}
x_486 = lean_ctor_get(x_484, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_484, 2);
lean_inc(x_487);
x_488 = lean_ctor_get(x_484, 3);
lean_inc(x_488);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 lean_ctor_release(x_484, 1);
 lean_ctor_release(x_484, 2);
 lean_ctor_release(x_484, 3);
 x_489 = x_484;
} else {
 lean_dec_ref(x_484);
 x_489 = lean_box(0);
}
x_490 = lean_array_size(x_488);
x_491 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_492 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2(x_1, x_490, x_491, x_488, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_515; 
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_492, 1);
lean_inc(x_494);
lean_dec(x_492);
x_515 = l_Array_isEmpty___redArg(x_493);
if (x_515 == 0)
{
x_495 = x_4;
x_496 = x_5;
x_497 = x_6;
x_498 = x_7;
x_499 = x_494;
goto block_514;
}
else
{
lean_object* x_516; lean_object* x_517; uint8_t x_518; 
lean_dec(x_493);
lean_dec(x_489);
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_4);
x_516 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__16;
x_517 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(x_516, x_5, x_6, x_7, x_494);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_518 = !lean_is_exclusive(x_517);
if (x_518 == 0)
{
return x_517;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_519 = lean_ctor_get(x_517, 0);
x_520 = lean_ctor_get(x_517, 1);
lean_inc(x_520);
lean_inc(x_519);
lean_dec(x_517);
x_521 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_521, 0, x_519);
lean_ctor_set(x_521, 1, x_520);
return x_521;
}
}
block_514:
{
lean_object* x_500; 
lean_inc(x_493);
x_500 = l_Lean_Compiler_LCNF_mkCasesResultType(x_493, x_495, x_496, x_497, x_498, x_499);
lean_dec(x_498);
lean_dec(x_497);
lean_dec(x_496);
lean_dec(x_495);
if (lean_obj_tag(x_500) == 0)
{
uint8_t x_501; 
x_501 = !lean_is_exclusive(x_500);
if (x_501 == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_502 = lean_ctor_get(x_500, 0);
if (lean_is_scalar(x_489)) {
 x_503 = lean_alloc_ctor(0, 4, 0);
} else {
 x_503 = x_489;
}
lean_ctor_set(x_503, 0, x_486);
lean_ctor_set(x_503, 1, x_502);
lean_ctor_set(x_503, 2, x_487);
lean_ctor_set(x_503, 3, x_493);
if (lean_is_scalar(x_485)) {
 x_504 = lean_alloc_ctor(4, 1, 0);
} else {
 x_504 = x_485;
}
lean_ctor_set(x_504, 0, x_503);
lean_ctor_set(x_500, 0, x_504);
return x_500;
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_505 = lean_ctor_get(x_500, 0);
x_506 = lean_ctor_get(x_500, 1);
lean_inc(x_506);
lean_inc(x_505);
lean_dec(x_500);
if (lean_is_scalar(x_489)) {
 x_507 = lean_alloc_ctor(0, 4, 0);
} else {
 x_507 = x_489;
}
lean_ctor_set(x_507, 0, x_486);
lean_ctor_set(x_507, 1, x_505);
lean_ctor_set(x_507, 2, x_487);
lean_ctor_set(x_507, 3, x_493);
if (lean_is_scalar(x_485)) {
 x_508 = lean_alloc_ctor(4, 1, 0);
} else {
 x_508 = x_485;
}
lean_ctor_set(x_508, 0, x_507);
x_509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_509, 0, x_508);
lean_ctor_set(x_509, 1, x_506);
return x_509;
}
}
else
{
uint8_t x_510; 
lean_dec(x_493);
lean_dec(x_489);
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_485);
x_510 = !lean_is_exclusive(x_500);
if (x_510 == 0)
{
return x_500;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_511 = lean_ctor_get(x_500, 0);
x_512 = lean_ctor_get(x_500, 1);
lean_inc(x_512);
lean_inc(x_511);
lean_dec(x_500);
x_513 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_513, 0, x_511);
lean_ctor_set(x_513, 1, x_512);
return x_513;
}
}
}
}
else
{
uint8_t x_522; 
lean_dec(x_489);
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_522 = !lean_is_exclusive(x_492);
if (x_522 == 0)
{
return x_492;
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_523 = lean_ctor_get(x_492, 0);
x_524 = lean_ctor_get(x_492, 1);
lean_inc(x_524);
lean_inc(x_523);
lean_dec(x_492);
x_525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_525, 0, x_523);
lean_ctor_set(x_525, 1, x_524);
return x_525;
}
}
}
case 5:
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_526 = lean_ctor_get(x_2, 0);
lean_inc(x_526);
lean_dec(x_2);
x_527 = lean_ctor_get(x_1, 0);
x_528 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_528, 0, x_526);
x_529 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12;
x_530 = lean_array_push(x_529, x_528);
lean_inc(x_527);
x_531 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_531, 0, x_527);
lean_ctor_set(x_531, 1, x_530);
x_532 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_8);
return x_532;
}
default: 
{
lean_object* x_533; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_533 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_533, 0, x_2);
lean_ctor_set(x_533, 1, x_8);
return x_533;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_11, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1(x_14, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_uget(x_4, x_3);
x_14 = lean_box(0);
x_15 = lean_array_uset(x_4, x_3, x_14);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_13, 2);
lean_inc(x_30);
x_16 = x_30;
goto block_29;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_13, 0);
lean_inc(x_31);
x_16 = x_31;
goto block_29;
}
block_29:
{
lean_object* x_17; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_16, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_13, x_18);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_23 = lean_array_uset(x_15, x_3, x_20);
x_3 = x_22;
x_4 = x_23;
x_10 = x_19;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_array_size(x_2);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0(x_1, x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = l_Lean_RBNode_fold___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(x_1, x_3);
lean_inc(x_4);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_box(0);
x_9 = lean_st_mk_ref(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 2);
x_15 = lean_ctor_get(x_2, 3);
x_16 = lean_ctor_get(x_2, 1);
lean_dec(x_16);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(x_1, x_15, x_10, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_10, x_19);
lean_dec(x_10);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_18);
x_24 = l_Lean_Compiler_LCNF_mkCasesResultType(x_18, x_3, x_4, x_5, x_6, x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
lean_ctor_set(x_2, 3, x_18);
lean_ctor_set(x_2, 1, x_26);
x_27 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_27, 0, x_2);
x_28 = l_Lean_RBNode_fold___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(x_27, x_22);
lean_dec(x_22);
lean_ctor_set_tag(x_20, 2);
lean_ctor_set(x_20, 1, x_28);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_24, 0, x_20);
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
lean_ctor_set(x_2, 3, x_18);
lean_ctor_set(x_2, 1, x_29);
x_31 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_31, 0, x_2);
x_32 = l_Lean_RBNode_fold___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(x_31, x_22);
lean_dec(x_22);
lean_ctor_set_tag(x_20, 2);
lean_ctor_set(x_20, 1, x_32);
lean_ctor_set(x_20, 0, x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_20);
lean_dec(x_22);
lean_dec(x_18);
lean_free_object(x_2);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_24);
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
x_38 = lean_ctor_get(x_20, 0);
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_20);
lean_inc(x_18);
x_40 = l_Lean_Compiler_LCNF_mkCasesResultType(x_18, x_3, x_4, x_5, x_6, x_39);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
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
lean_ctor_set(x_2, 3, x_18);
lean_ctor_set(x_2, 1, x_41);
x_44 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_44, 0, x_2);
x_45 = l_Lean_RBNode_fold___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(x_44, x_38);
lean_dec(x_38);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
if (lean_is_scalar(x_43)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_43;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_38);
lean_dec(x_18);
lean_free_object(x_2);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_1);
x_48 = lean_ctor_get(x_40, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_50 = x_40;
} else {
 lean_dec_ref(x_40);
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
else
{
uint8_t x_52; 
lean_free_object(x_2);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_17);
if (x_52 == 0)
{
return x_17;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_17, 0);
x_54 = lean_ctor_get(x_17, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_17);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_2, 0);
x_57 = lean_ctor_get(x_2, 2);
x_58 = lean_ctor_get(x_2, 3);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_59 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(x_1, x_58, x_10, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_st_ref_get(x_10, x_61);
lean_dec(x_10);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
lean_inc(x_60);
x_66 = l_Lean_Compiler_LCNF_mkCasesResultType(x_60, x_3, x_4, x_5, x_6, x_64);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_70, 0, x_56);
lean_ctor_set(x_70, 1, x_67);
lean_ctor_set(x_70, 2, x_57);
lean_ctor_set(x_70, 3, x_60);
x_71 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = l_Lean_RBNode_fold___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(x_71, x_63);
lean_dec(x_63);
if (lean_is_scalar(x_65)) {
 x_73 = lean_alloc_ctor(2, 2, 0);
} else {
 x_73 = x_65;
 lean_ctor_set_tag(x_73, 2);
}
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_72);
if (lean_is_scalar(x_69)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_69;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_68);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_1);
x_75 = lean_ctor_get(x_66, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_66, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_77 = x_66;
} else {
 lean_dec_ref(x_66);
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
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_79 = lean_ctor_get(x_59, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_59, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_81 = x_59;
} else {
 lean_dec_ref(x_59);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_fold___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_21; 
x_21 = lean_usize_dec_eq(x_2, x_3);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_4);
x_22 = lean_array_uget(x_1, x_2);
switch (lean_obj_tag(x_22)) {
case 2:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_23, x_5, x_6);
lean_dec(x_23);
x_7 = x_24;
goto block_13;
}
case 3:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_26, x_5, x_6);
lean_dec(x_26);
x_7 = x_27;
goto block_13;
}
case 4:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
lean_dec(x_22);
x_29 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_28, x_5, x_6);
lean_dec(x_28);
x_7 = x_29;
goto block_13;
}
default: 
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_14 = x_30;
x_15 = x_5;
x_16 = x_6;
goto block_20;
}
}
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_6);
return x_31;
}
block_13:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_8;
x_6 = x_9;
goto _start;
}
block_20:
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_box(1);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(x_14, x_18, x_15, x_16);
lean_dec(x_14);
x_7 = x_19;
goto block_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_2);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement;
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_2, x_24);
x_26 = lean_array_get(x_23, x_1, x_25);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
x_2 = x_25;
x_3 = x_28;
goto _start;
}
case 1:
{
lean_object* x_30; 
lean_dec(x_25);
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_9 = x_30;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
x_14 = x_8;
goto block_19;
}
case 2:
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
x_2 = x_25;
x_3 = x_32;
goto _start;
}
case 3:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_2);
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
x_38 = lean_name_eq(x_37, x_36);
lean_dec(x_36);
lean_dec(x_37);
if (x_38 == 0)
{
lean_dec(x_35);
lean_dec(x_34);
x_2 = x_25;
goto _start;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_3);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_3, 0);
lean_dec(x_41);
x_42 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_34, x_5, x_8);
lean_dec(x_34);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
lean_ctor_set_tag(x_3, 4);
lean_ctor_set(x_3, 0, x_35);
x_2 = x_25;
x_8 = x_43;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_3);
x_45 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_34, x_5, x_8);
lean_dec(x_34);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_47, 0, x_35);
x_2 = x_25;
x_3 = x_47;
x_8 = x_46;
goto _start;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_49 = lean_ctor_get(x_26, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_26, 1);
lean_inc(x_50);
lean_dec(x_26);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 2);
lean_inc(x_53);
lean_inc(x_53);
x_54 = l_Lean_Expr_headBeta(x_53);
x_55 = l_Lean_Expr_isForall(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_2);
x_56 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__14;
x_57 = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(x_49, x_3, x_56, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_60 = l_Lean_Compiler_LCNF_ToLCNF_bindCases(x_58, x_50, x_4, x_5, x_6, x_7, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_2 = x_25;
x_3 = x_61;
x_8 = x_62;
goto _start;
}
else
{
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_60;
}
}
else
{
uint8_t x_64; 
lean_dec(x_50);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_57);
if (x_64 == 0)
{
return x_57;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_57, 0);
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_57);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec(x_25);
x_68 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_49, x_5, x_8);
lean_dec(x_49);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_st_ref_take(x_5, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_71, 0);
x_75 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2;
x_76 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_76, 0, x_50);
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_51);
lean_ctor_set(x_77, 1, x_52);
lean_ctor_set(x_77, 2, x_75);
lean_ctor_set(x_77, 3, x_53);
lean_ctor_set(x_77, 4, x_76);
lean_inc(x_77);
x_78 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_74, x_77);
lean_ctor_set(x_71, 0, x_78);
x_79 = lean_st_ref_set(x_5, x_71, x_72);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_81 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_77, x_4, x_5, x_6, x_7, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_9 = x_82;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
x_14 = x_83;
goto block_19;
}
else
{
uint8_t x_84; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_81);
if (x_84 == 0)
{
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_81, 0);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_81);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_88 = lean_ctor_get(x_71, 0);
x_89 = lean_ctor_get(x_71, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_71);
x_90 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2;
x_91 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_91, 0, x_50);
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_51);
lean_ctor_set(x_92, 1, x_52);
lean_ctor_set(x_92, 2, x_90);
lean_ctor_set(x_92, 3, x_53);
lean_ctor_set(x_92, 4, x_91);
lean_inc(x_92);
x_93 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_88, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_89);
x_95 = lean_st_ref_set(x_5, x_94, x_72);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_97 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_92, x_4, x_5, x_6, x_7, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_9 = x_98;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
x_14 = x_99;
goto block_19;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = lean_ctor_get(x_97, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_102 = x_97;
} else {
 lean_dec_ref(x_97);
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
}
default: 
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_25);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_104 = x_26;
} else {
 lean_dec_ref(x_26);
 x_104 = lean_box(0);
}
lean_inc(x_3);
x_105 = l_Lean_Compiler_LCNF_Code_inferType(x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
x_113 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_3, x_5, x_107);
lean_dec(x_3);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_115 = l_Array_toSubarray___redArg(x_1, x_20, x_2);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 2);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_nat_dec_lt(x_117, x_118);
if (x_119 == 0)
{
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_5);
x_109 = x_114;
goto block_112;
}
else
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_array_get_size(x_116);
x_121 = lean_nat_dec_le(x_118, x_120);
lean_dec(x_120);
if (x_121 == 0)
{
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_5);
x_109 = x_114;
goto block_112;
}
else
{
lean_object* x_122; size_t x_123; size_t x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_box(0);
x_123 = lean_usize_of_nat(x_117);
lean_dec(x_117);
x_124 = lean_usize_of_nat(x_118);
lean_dec(x_118);
x_125 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___redArg(x_116, x_123, x_124, x_122, x_5, x_114);
lean_dec(x_5);
lean_dec(x_116);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_109 = x_126;
goto block_112;
}
}
block_112:
{
lean_object* x_110; lean_object* x_111; 
if (lean_is_scalar(x_104)) {
 x_110 = lean_alloc_ctor(6, 1, 0);
} else {
 x_110 = x_104;
 lean_ctor_set_tag(x_110, 6);
}
lean_ctor_set(x_110, 0, x_106);
if (lean_is_scalar(x_108)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_108;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
else
{
uint8_t x_127; 
lean_dec(x_104);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_105);
if (x_127 == 0)
{
return x_105;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_105, 0);
x_129 = lean_ctor_get(x_105, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_105);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
}
block_19:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_3);
x_2 = x_16;
x_3 = x_17;
x_4 = x_10;
x_5 = x_11;
x_6 = x_12;
x_7 = x_13;
x_8 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__3;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__2;
x_3 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__1;
x_4 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__7() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5;
x_4 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__6;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__8;
x_2 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__9;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__7;
x_3 = lean_box(0);
x_4 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__4;
x_5 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; 
x_1 = lean_box(2);
x_2 = lean_box(0);
x_3 = lean_box(1);
x_4 = lean_box(1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 0, 18);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 0, x_7);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 1, x_8);
x_9 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 2, x_9);
x_10 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 3, x_10);
x_11 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 4, x_11);
x_12 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 5, x_12);
x_13 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 6, x_13);
x_14 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 7, x_14);
x_15 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 8, x_15);
x_16 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, 9, x_16);
x_17 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, 10, x_17);
x_18 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 11, x_18);
x_19 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 12, x_19);
x_20 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 13, x_20);
x_21 = lean_unbox(x_1);
lean_ctor_set_uint8(x_6, 14, x_21);
x_22 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 15, x_22);
x_23 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 16, x_23);
x_24 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 17, x_24);
return x_6;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_2 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_6 = lean_st_ref_get(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_12 = lean_st_mk_ref(x_11, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_box(0);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_18 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_19 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13;
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_9);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set(x_22, 4, x_20);
lean_ctor_set(x_22, 5, x_10);
lean_ctor_set(x_22, 6, x_21);
lean_ctor_set_uint64(x_22, sizeof(void*)*7, x_18);
x_23 = lean_unbox(x_16);
lean_ctor_set_uint8(x_22, sizeof(void*)*7 + 8, x_23);
x_24 = lean_unbox(x_16);
lean_ctor_set_uint8(x_22, sizeof(void*)*7 + 9, x_24);
x_25 = lean_unbox(x_16);
lean_ctor_set_uint8(x_22, sizeof(void*)*7 + 10, x_25);
lean_inc(x_13);
x_26 = lean_apply_5(x_1, x_22, x_13, x_3, x_4, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_13, x_28);
lean_dec(x_13);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_dec(x_13);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_15 = lean_st_mk_ref(x_14, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_box(0);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_21 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_22 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13;
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set(x_25, 5, x_13);
lean_ctor_set(x_25, 6, x_24);
lean_ctor_set_uint64(x_25, sizeof(void*)*7, x_21);
x_26 = lean_unbox(x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 8, x_26);
x_27 = lean_unbox(x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 9, x_27);
x_28 = lean_unbox(x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 10, x_28);
lean_inc(x_16);
x_29 = lean_apply_5(x_2, x_25, x_16, x_6, x_7, x_17);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_st_ref_get(x_16, x_31);
lean_dec(x_16);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_30);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_dec(x_16);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 4);
x_9 = lean_array_push(x_8, x_1);
lean_ctor_set(x_5, 4, x_9);
x_10 = lean_st_ref_set(x_2, x_5, x_6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_ctor_get(x_5, 3);
x_21 = lean_ctor_get(x_5, 4);
x_22 = lean_ctor_get(x_5, 5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_23 = lean_array_push(x_21, x_1);
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set(x_24, 4, x_23);
lean_ctor_set(x_24, 5, x_22);
x_25 = lean_st_ref_set(x_2, x_24, x_6);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_pushElement(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Compiler_LCNF_mkAuxParam(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_13, x_2, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_array_get_size(x_38);
lean_dec(x_38);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_eq(x_39, x_40);
lean_dec(x_39);
if (x_41 == 0)
{
lean_dec(x_37);
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
x_14 = x_8;
goto block_36;
}
else
{
uint8_t x_42; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_1);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_1, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_1, 0);
lean_dec(x_44);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_8);
return x_1;
}
else
{
lean_object* x_45; 
lean_dec(x_1);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_8);
return x_45;
}
}
}
else
{
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
x_14 = x_8;
goto block_36;
}
block_36:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(x_2, x_11, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_18 = l_Lean_Compiler_LCNF_LetValue_inferType(x_1, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Compiler_LCNF_mkLetDecl(x_16, x_19, x_1, x_10, x_11, x_12, x_13, x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_22);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_24, x_9, x_23);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
lean_dec(x_22);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
return x_18;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_8 = x_22;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
goto block_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_23 = lean_box(1);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_23, x_24, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_8 = x_26;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_27;
goto block_21;
}
else
{
uint8_t x_28; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
block_21:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_st_ref_get(x_9, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 4);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_19, 0, x_8);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode(x_18, x_19, x_10, x_11, x_12, x_13, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toCode(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__4() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__2;
x_4 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__3;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__4;
x_3 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__9;
x_3 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__8;
x_4 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__6;
x_5 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__5;
x_6 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set(x_6, 4, x_2);
lean_ctor_set(x_6, 5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__10;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = lean_apply_6(x_1, x_9, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_9, x_13);
lean_dec(x_9);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_dec(x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
case 3:
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_1);
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
case 7:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 2);
x_2 = x_7;
goto _start;
}
case 8:
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_1);
x_9 = lean_box(2);
x_10 = lean_unbox(x_9);
return x_10;
}
case 10:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_2, 1);
x_2 = x_11;
goto _start;
}
default: 
{
lean_object* x_13; 
x_13 = l_Lean_Expr_getAppFn(x_2);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_13);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
case 4:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Environment_find_x3f(x_1, x_16, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_box(2);
x_21 = lean_unbox(x_20);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
if (lean_obj_tag(x_22) == 5)
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_22);
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_22);
x_25 = lean_box(2);
x_26 = lean_unbox(x_25);
return x_26;
}
}
}
default: 
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_13);
lean_dec(x_1);
x_27 = lean_box(2);
x_28 = lean_unbox(x_27);
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_23; lean_object* x_24; lean_object* x_107; uint8_t x_108; 
x_107 = lean_st_ref_get(x_4, x_5);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = lean_ctor_get(x_107, 1);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
lean_dec(x_109);
x_112 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(x_111, x_1);
switch (x_112) {
case 0:
{
lean_object* x_113; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_113 = lean_box(0);
lean_ctor_set(x_107, 0, x_113);
return x_107;
}
case 1:
{
lean_object* x_114; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_114 = lean_box(1);
lean_ctor_set(x_107, 0, x_114);
return x_107;
}
default: 
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
lean_free_object(x_107);
x_115 = lean_st_ref_get(x_2, x_110);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_116, 3);
lean_inc(x_117);
lean_dec(x_116);
x_118 = !lean_is_exclusive(x_115);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint64_t x_123; uint64_t x_124; uint64_t x_125; uint64_t x_126; uint64_t x_127; uint64_t x_128; uint64_t x_129; size_t x_130; size_t x_131; size_t x_132; size_t x_133; size_t x_134; lean_object* x_135; lean_object* x_136; 
x_119 = lean_ctor_get(x_115, 1);
x_120 = lean_ctor_get(x_115, 0);
lean_dec(x_120);
x_121 = lean_ctor_get(x_117, 1);
lean_inc(x_121);
lean_dec(x_117);
x_122 = lean_array_get_size(x_121);
x_123 = l_Lean_Expr_hash(x_1);
x_124 = 32;
x_125 = lean_uint64_shift_right(x_123, x_124);
x_126 = lean_uint64_xor(x_123, x_125);
x_127 = 16;
x_128 = lean_uint64_shift_right(x_126, x_127);
x_129 = lean_uint64_xor(x_126, x_128);
x_130 = lean_uint64_to_usize(x_129);
x_131 = lean_usize_of_nat(x_122);
lean_dec(x_122);
x_132 = 1;
x_133 = lean_usize_sub(x_131, x_132);
x_134 = lean_usize_land(x_130, x_133);
x_135 = lean_array_uget(x_121, x_134);
lean_dec(x_121);
x_136 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__1___redArg(x_1, x_135);
lean_dec(x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint64_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; lean_object* x_157; 
lean_free_object(x_115);
x_137 = lean_st_ref_get(x_2, x_119);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_box(0);
x_141 = lean_unsigned_to_nat(0u);
x_142 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_143 = lean_st_mk_ref(x_142, x_139);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_ctor_get(x_138, 0);
lean_inc(x_146);
lean_dec(x_138);
x_147 = lean_box(0);
x_148 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_149 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_150 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13;
x_151 = lean_box(0);
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_153, 0, x_148);
lean_ctor_set(x_153, 1, x_140);
lean_ctor_set(x_153, 2, x_146);
lean_ctor_set(x_153, 3, x_150);
lean_ctor_set(x_153, 4, x_151);
lean_ctor_set(x_153, 5, x_141);
lean_ctor_set(x_153, 6, x_152);
lean_ctor_set_uint64(x_153, sizeof(void*)*7, x_149);
x_154 = lean_unbox(x_147);
lean_ctor_set_uint8(x_153, sizeof(void*)*7 + 8, x_154);
x_155 = lean_unbox(x_147);
lean_ctor_set_uint8(x_153, sizeof(void*)*7 + 9, x_155);
x_156 = lean_unbox(x_147);
lean_ctor_set_uint8(x_153, sizeof(void*)*7 + 10, x_156);
lean_inc(x_144);
lean_inc(x_1);
x_157 = l_Lean_Meta_isTypeFormerType(x_1, x_153, x_144, x_3, x_4, x_145);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_st_ref_get(x_144, x_159);
lean_dec(x_144);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = lean_unbox(x_158);
lean_dec(x_158);
x_23 = x_162;
x_24 = x_161;
goto block_106;
}
else
{
lean_dec(x_144);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_163 = lean_ctor_get(x_157, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_157, 1);
lean_inc(x_164);
lean_dec(x_157);
x_165 = lean_unbox(x_163);
lean_dec(x_163);
x_23 = x_165;
x_24 = x_164;
goto block_106;
}
else
{
lean_dec(x_1);
return x_157;
}
}
}
else
{
lean_object* x_166; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_166 = lean_ctor_get(x_136, 0);
lean_inc(x_166);
lean_dec(x_136);
lean_ctor_set(x_115, 0, x_166);
return x_115;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint64_t x_170; uint64_t x_171; uint64_t x_172; uint64_t x_173; uint64_t x_174; uint64_t x_175; uint64_t x_176; size_t x_177; size_t x_178; size_t x_179; size_t x_180; size_t x_181; lean_object* x_182; lean_object* x_183; 
x_167 = lean_ctor_get(x_115, 1);
lean_inc(x_167);
lean_dec(x_115);
x_168 = lean_ctor_get(x_117, 1);
lean_inc(x_168);
lean_dec(x_117);
x_169 = lean_array_get_size(x_168);
x_170 = l_Lean_Expr_hash(x_1);
x_171 = 32;
x_172 = lean_uint64_shift_right(x_170, x_171);
x_173 = lean_uint64_xor(x_170, x_172);
x_174 = 16;
x_175 = lean_uint64_shift_right(x_173, x_174);
x_176 = lean_uint64_xor(x_173, x_175);
x_177 = lean_uint64_to_usize(x_176);
x_178 = lean_usize_of_nat(x_169);
lean_dec(x_169);
x_179 = 1;
x_180 = lean_usize_sub(x_178, x_179);
x_181 = lean_usize_land(x_177, x_180);
x_182 = lean_array_uget(x_168, x_181);
lean_dec(x_168);
x_183 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__1___redArg(x_1, x_182);
lean_dec(x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint64_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; lean_object* x_204; 
x_184 = lean_st_ref_get(x_2, x_167);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_box(0);
x_188 = lean_unsigned_to_nat(0u);
x_189 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_190 = lean_st_mk_ref(x_189, x_186);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_ctor_get(x_185, 0);
lean_inc(x_193);
lean_dec(x_185);
x_194 = lean_box(0);
x_195 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_196 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_197 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13;
x_198 = lean_box(0);
x_199 = lean_box(0);
x_200 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_200, 0, x_195);
lean_ctor_set(x_200, 1, x_187);
lean_ctor_set(x_200, 2, x_193);
lean_ctor_set(x_200, 3, x_197);
lean_ctor_set(x_200, 4, x_198);
lean_ctor_set(x_200, 5, x_188);
lean_ctor_set(x_200, 6, x_199);
lean_ctor_set_uint64(x_200, sizeof(void*)*7, x_196);
x_201 = lean_unbox(x_194);
lean_ctor_set_uint8(x_200, sizeof(void*)*7 + 8, x_201);
x_202 = lean_unbox(x_194);
lean_ctor_set_uint8(x_200, sizeof(void*)*7 + 9, x_202);
x_203 = lean_unbox(x_194);
lean_ctor_set_uint8(x_200, sizeof(void*)*7 + 10, x_203);
lean_inc(x_191);
lean_inc(x_1);
x_204 = l_Lean_Meta_isTypeFormerType(x_1, x_200, x_191, x_3, x_4, x_192);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_st_ref_get(x_191, x_206);
lean_dec(x_191);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
lean_dec(x_207);
x_209 = lean_unbox(x_205);
lean_dec(x_205);
x_23 = x_209;
x_24 = x_208;
goto block_106;
}
else
{
lean_dec(x_191);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_210 = lean_ctor_get(x_204, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_204, 1);
lean_inc(x_211);
lean_dec(x_204);
x_212 = lean_unbox(x_210);
lean_dec(x_210);
x_23 = x_212;
x_24 = x_211;
goto block_106;
}
else
{
lean_dec(x_1);
return x_204;
}
}
}
else
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_213 = lean_ctor_get(x_183, 0);
lean_inc(x_213);
lean_dec(x_183);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_167);
return x_214;
}
}
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_215 = lean_ctor_get(x_107, 0);
x_216 = lean_ctor_get(x_107, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_107);
x_217 = lean_ctor_get(x_215, 0);
lean_inc(x_217);
lean_dec(x_215);
x_218 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(x_217, x_1);
switch (x_218) {
case 0:
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_219 = lean_box(0);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_216);
return x_220;
}
case 1:
{
lean_object* x_221; lean_object* x_222; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_221 = lean_box(1);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_216);
return x_222;
}
default: 
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint64_t x_230; uint64_t x_231; uint64_t x_232; uint64_t x_233; uint64_t x_234; uint64_t x_235; uint64_t x_236; size_t x_237; size_t x_238; size_t x_239; size_t x_240; size_t x_241; lean_object* x_242; lean_object* x_243; 
x_223 = lean_st_ref_get(x_2, x_216);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_224, 3);
lean_inc(x_225);
lean_dec(x_224);
x_226 = lean_ctor_get(x_223, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_227 = x_223;
} else {
 lean_dec_ref(x_223);
 x_227 = lean_box(0);
}
x_228 = lean_ctor_get(x_225, 1);
lean_inc(x_228);
lean_dec(x_225);
x_229 = lean_array_get_size(x_228);
x_230 = l_Lean_Expr_hash(x_1);
x_231 = 32;
x_232 = lean_uint64_shift_right(x_230, x_231);
x_233 = lean_uint64_xor(x_230, x_232);
x_234 = 16;
x_235 = lean_uint64_shift_right(x_233, x_234);
x_236 = lean_uint64_xor(x_233, x_235);
x_237 = lean_uint64_to_usize(x_236);
x_238 = lean_usize_of_nat(x_229);
lean_dec(x_229);
x_239 = 1;
x_240 = lean_usize_sub(x_238, x_239);
x_241 = lean_usize_land(x_237, x_240);
x_242 = lean_array_uget(x_228, x_241);
lean_dec(x_228);
x_243 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__1___redArg(x_1, x_242);
lean_dec(x_242);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint64_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; uint8_t x_262; uint8_t x_263; lean_object* x_264; 
lean_dec(x_227);
x_244 = lean_st_ref_get(x_2, x_226);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_box(0);
x_248 = lean_unsigned_to_nat(0u);
x_249 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_250 = lean_st_mk_ref(x_249, x_246);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_ctor_get(x_245, 0);
lean_inc(x_253);
lean_dec(x_245);
x_254 = lean_box(0);
x_255 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_256 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_257 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13;
x_258 = lean_box(0);
x_259 = lean_box(0);
x_260 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_260, 0, x_255);
lean_ctor_set(x_260, 1, x_247);
lean_ctor_set(x_260, 2, x_253);
lean_ctor_set(x_260, 3, x_257);
lean_ctor_set(x_260, 4, x_258);
lean_ctor_set(x_260, 5, x_248);
lean_ctor_set(x_260, 6, x_259);
lean_ctor_set_uint64(x_260, sizeof(void*)*7, x_256);
x_261 = lean_unbox(x_254);
lean_ctor_set_uint8(x_260, sizeof(void*)*7 + 8, x_261);
x_262 = lean_unbox(x_254);
lean_ctor_set_uint8(x_260, sizeof(void*)*7 + 9, x_262);
x_263 = lean_unbox(x_254);
lean_ctor_set_uint8(x_260, sizeof(void*)*7 + 10, x_263);
lean_inc(x_251);
lean_inc(x_1);
x_264 = l_Lean_Meta_isTypeFormerType(x_1, x_260, x_251, x_3, x_4, x_252);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = lean_st_ref_get(x_251, x_266);
lean_dec(x_251);
x_268 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
lean_dec(x_267);
x_269 = lean_unbox(x_265);
lean_dec(x_265);
x_23 = x_269;
x_24 = x_268;
goto block_106;
}
else
{
lean_dec(x_251);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_270 = lean_ctor_get(x_264, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_264, 1);
lean_inc(x_271);
lean_dec(x_264);
x_272 = lean_unbox(x_270);
lean_dec(x_270);
x_23 = x_272;
x_24 = x_271;
goto block_106;
}
else
{
lean_dec(x_1);
return x_264;
}
}
}
else
{
lean_object* x_273; lean_object* x_274; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_273 = lean_ctor_get(x_243, 0);
lean_inc(x_273);
lean_dec(x_243);
if (lean_is_scalar(x_227)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_227;
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_226);
return x_274;
}
}
}
}
block_22:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_14, 4, x_7);
lean_ctor_set(x_14, 5, x_8);
x_15 = lean_st_ref_set(x_2, x_14, x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(x_9);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(x_9);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
block_106:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_25 = lean_st_ref_take(x_2, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_26, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 5);
lean_inc(x_33);
lean_dec(x_26);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; size_t x_45; size_t x_46; size_t x_47; size_t x_48; size_t x_49; lean_object* x_50; uint8_t x_51; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
x_37 = lean_array_get_size(x_36);
x_38 = l_Lean_Expr_hash(x_1);
x_39 = 32;
x_40 = lean_uint64_shift_right(x_38, x_39);
x_41 = lean_uint64_xor(x_38, x_40);
x_42 = 16;
x_43 = lean_uint64_shift_right(x_41, x_42);
x_44 = lean_uint64_xor(x_41, x_43);
x_45 = lean_uint64_to_usize(x_44);
x_46 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_47 = 1;
x_48 = lean_usize_sub(x_46, x_47);
x_49 = lean_usize_land(x_45, x_48);
x_50 = lean_array_uget(x_36, x_49);
x_51 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_1, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_35, x_52);
lean_dec(x_35);
x_54 = lean_box(x_23);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_50);
x_56 = lean_array_uset(x_36, x_49, x_55);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_mul(x_53, x_57);
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_div(x_58, x_59);
lean_dec(x_58);
x_61 = lean_array_get_size(x_56);
x_62 = lean_nat_dec_le(x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_56);
lean_ctor_set(x_27, 1, x_63);
lean_ctor_set(x_27, 0, x_53);
x_6 = x_28;
x_7 = x_32;
x_8 = x_33;
x_9 = x_23;
x_10 = x_31;
x_11 = x_30;
x_12 = x_29;
x_13 = x_27;
goto block_22;
}
else
{
lean_ctor_set(x_27, 1, x_56);
lean_ctor_set(x_27, 0, x_53);
x_6 = x_28;
x_7 = x_32;
x_8 = x_33;
x_9 = x_23;
x_10 = x_31;
x_11 = x_30;
x_12 = x_29;
x_13 = x_27;
goto block_22;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_box(0);
x_65 = lean_array_uset(x_36, x_49, x_64);
x_66 = lean_box(x_23);
x_67 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at___Lean_Compiler_SpecState_addEntry_spec__0_spec__0___redArg(x_1, x_66, x_50);
x_68 = lean_array_uset(x_65, x_49, x_67);
lean_ctor_set(x_27, 1, x_68);
x_6 = x_28;
x_7 = x_32;
x_8 = x_33;
x_9 = x_23;
x_10 = x_31;
x_11 = x_30;
x_12 = x_29;
x_13 = x_27;
goto block_22;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; size_t x_79; size_t x_80; size_t x_81; size_t x_82; size_t x_83; lean_object* x_84; uint8_t x_85; 
x_69 = lean_ctor_get(x_27, 0);
x_70 = lean_ctor_get(x_27, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_27);
x_71 = lean_array_get_size(x_70);
x_72 = l_Lean_Expr_hash(x_1);
x_73 = 32;
x_74 = lean_uint64_shift_right(x_72, x_73);
x_75 = lean_uint64_xor(x_72, x_74);
x_76 = 16;
x_77 = lean_uint64_shift_right(x_75, x_76);
x_78 = lean_uint64_xor(x_75, x_77);
x_79 = lean_uint64_to_usize(x_78);
x_80 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_81 = 1;
x_82 = lean_usize_sub(x_80, x_81);
x_83 = lean_usize_land(x_79, x_82);
x_84 = lean_array_uget(x_70, x_83);
x_85 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_1, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_add(x_69, x_86);
lean_dec(x_69);
x_88 = lean_box(x_23);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 2, x_84);
x_90 = lean_array_uset(x_70, x_83, x_89);
x_91 = lean_unsigned_to_nat(4u);
x_92 = lean_nat_mul(x_87, x_91);
x_93 = lean_unsigned_to_nat(3u);
x_94 = lean_nat_div(x_92, x_93);
lean_dec(x_92);
x_95 = lean_array_get_size(x_90);
x_96 = lean_nat_dec_le(x_94, x_95);
lean_dec(x_95);
lean_dec(x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_90);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_87);
lean_ctor_set(x_98, 1, x_97);
x_6 = x_28;
x_7 = x_32;
x_8 = x_33;
x_9 = x_23;
x_10 = x_31;
x_11 = x_30;
x_12 = x_29;
x_13 = x_98;
goto block_22;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_87);
lean_ctor_set(x_99, 1, x_90);
x_6 = x_28;
x_7 = x_32;
x_8 = x_33;
x_9 = x_23;
x_10 = x_31;
x_11 = x_30;
x_12 = x_29;
x_13 = x_99;
goto block_22;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_box(0);
x_101 = lean_array_uset(x_70, x_83, x_100);
x_102 = lean_box(x_23);
x_103 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at___Lean_Compiler_SpecState_addEntry_spec__0_spec__0___redArg(x_1, x_102, x_84);
x_104 = lean_array_uset(x_101, x_83, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_69);
lean_ctor_set(x_105, 1, x_104);
x_6 = x_28;
x_7 = x_32;
x_8 = x_33;
x_9 = x_23;
x_10 = x_31;
x_11 = x_30;
x_12 = x_29;
x_13 = x_105;
goto block_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_1, x_2, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_st_ref_get(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_1, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_9, 2);
lean_inc(x_14);
lean_dec(x_9);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_12, 5);
lean_dec(x_16);
x_17 = lean_ctor_get(x_12, 4);
lean_dec(x_17);
x_18 = lean_ctor_get(x_12, 2);
lean_dec(x_18);
x_19 = lean_ctor_get(x_12, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
lean_ctor_set(x_12, 5, x_5);
lean_ctor_set(x_12, 4, x_4);
lean_ctor_set(x_12, 2, x_14);
lean_ctor_set(x_12, 1, x_3);
lean_ctor_set(x_12, 0, x_2);
x_21 = lean_st_ref_set(x_1, x_12, x_13);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_12, 3);
lean_inc(x_26);
lean_dec(x_12);
x_27 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_3);
lean_ctor_set(x_27, 2, x_14);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_27, 4, x_4);
lean_ctor_set(x_27, 5, x_5);
x_28 = lean_st_ref_set(x_1, x_27, x_13);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_st_ref_get(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_take(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_12, 4);
lean_dec(x_15);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__9;
lean_ctor_set(x_12, 4, x_16);
x_17 = lean_st_ref_set(x_2, x_12, x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_9, 4);
lean_inc(x_21);
x_22 = lean_ctor_get(x_9, 5);
lean_inc(x_22);
lean_dec(x_9);
lean_inc(x_2);
x_23 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_24);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(x_2, x_19, x_20, x_21, x_22, x_26, x_25);
lean_dec(x_26);
lean_dec(x_2);
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_dec(x_23);
x_34 = lean_box(0);
x_35 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(x_2, x_19, x_20, x_21, x_22, x_34, x_33);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 0, x_32);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_40 = lean_ctor_get(x_12, 0);
x_41 = lean_ctor_get(x_12, 1);
x_42 = lean_ctor_get(x_12, 2);
x_43 = lean_ctor_get(x_12, 3);
x_44 = lean_ctor_get(x_12, 5);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_12);
x_45 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__9;
x_46 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_41);
lean_ctor_set(x_46, 2, x_42);
lean_ctor_set(x_46, 3, x_43);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set(x_46, 5, x_44);
x_47 = lean_st_ref_set(x_2, x_46, x_13);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get(x_9, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_9, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_9, 4);
lean_inc(x_51);
x_52 = lean_ctor_get(x_9, 5);
lean_inc(x_52);
lean_dec(x_9);
lean_inc(x_2);
x_53 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_48);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_54);
x_57 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(x_2, x_49, x_50, x_51, x_52, x_56, x_55);
lean_dec(x_56);
lean_dec(x_2);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_53, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_53, 1);
lean_inc(x_62);
lean_dec(x_53);
x_63 = lean_box(0);
x_64 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(x_2, x_49, x_50, x_51, x_52, x_63, x_62);
lean_dec(x_2);
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
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
 lean_ctor_set_tag(x_67, 1);
}
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_anyExpr;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__0;
return x_6;
}
}
else
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 5);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_replace_expr(x_8, x_1);
lean_dec(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_ctor_get(x_10, 5);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_replace_expr(x_13, x_1);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_21; lean_object* x_22; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_104 = lean_st_ref_get(x_2, x_5);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_105, 2);
lean_inc(x_106);
lean_dec(x_105);
x_107 = !lean_is_exclusive(x_104);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; uint64_t x_118; size_t x_119; size_t x_120; size_t x_121; size_t x_122; size_t x_123; lean_object* x_124; lean_object* x_125; 
x_108 = lean_ctor_get(x_104, 1);
x_109 = lean_ctor_get(x_104, 0);
lean_dec(x_109);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
lean_dec(x_106);
x_111 = lean_array_get_size(x_110);
x_112 = l_Lean_Expr_hash(x_1);
x_113 = 32;
x_114 = lean_uint64_shift_right(x_112, x_113);
x_115 = lean_uint64_xor(x_112, x_114);
x_116 = 16;
x_117 = lean_uint64_shift_right(x_115, x_116);
x_118 = lean_uint64_xor(x_115, x_117);
x_119 = lean_uint64_to_usize(x_118);
x_120 = lean_usize_of_nat(x_111);
lean_dec(x_111);
x_121 = 1;
x_122 = lean_usize_sub(x_120, x_121);
x_123 = lean_usize_land(x_119, x_122);
x_124 = lean_array_uget(x_110, x_123);
lean_dec(x_110);
x_125 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__1___redArg(x_1, x_124);
lean_dec(x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint64_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; lean_object* x_146; 
lean_free_object(x_104);
x_126 = lean_st_ref_get(x_2, x_108);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_box(0);
x_130 = lean_unsigned_to_nat(0u);
x_131 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_132 = lean_st_mk_ref(x_131, x_128);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_127, 0);
lean_inc(x_135);
lean_dec(x_127);
x_136 = lean_box(0);
x_137 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_138 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_139 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13;
x_140 = lean_box(0);
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_142, 0, x_137);
lean_ctor_set(x_142, 1, x_129);
lean_ctor_set(x_142, 2, x_135);
lean_ctor_set(x_142, 3, x_139);
lean_ctor_set(x_142, 4, x_140);
lean_ctor_set(x_142, 5, x_130);
lean_ctor_set(x_142, 6, x_141);
lean_ctor_set_uint64(x_142, sizeof(void*)*7, x_138);
x_143 = lean_unbox(x_136);
lean_ctor_set_uint8(x_142, sizeof(void*)*7 + 8, x_143);
x_144 = lean_unbox(x_136);
lean_ctor_set_uint8(x_142, sizeof(void*)*7 + 9, x_144);
x_145 = lean_unbox(x_136);
lean_ctor_set_uint8(x_142, sizeof(void*)*7 + 10, x_145);
lean_inc(x_133);
lean_inc(x_1);
x_146 = l_Lean_Compiler_LCNF_toLCNFType(x_1, x_142, x_133, x_3, x_4, x_134);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_st_ref_get(x_133, x_148);
lean_dec(x_133);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_21 = x_147;
x_22 = x_150;
goto block_103;
}
else
{
lean_dec(x_133);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_146, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_146, 1);
lean_inc(x_152);
lean_dec(x_146);
x_21 = x_151;
x_22 = x_152;
goto block_103;
}
else
{
lean_dec(x_1);
return x_146;
}
}
}
else
{
lean_object* x_153; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_153 = lean_ctor_get(x_125, 0);
lean_inc(x_153);
lean_dec(x_125);
lean_ctor_set(x_104, 0, x_153);
return x_104;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint64_t x_157; uint64_t x_158; uint64_t x_159; uint64_t x_160; uint64_t x_161; uint64_t x_162; uint64_t x_163; size_t x_164; size_t x_165; size_t x_166; size_t x_167; size_t x_168; lean_object* x_169; lean_object* x_170; 
x_154 = lean_ctor_get(x_104, 1);
lean_inc(x_154);
lean_dec(x_104);
x_155 = lean_ctor_get(x_106, 1);
lean_inc(x_155);
lean_dec(x_106);
x_156 = lean_array_get_size(x_155);
x_157 = l_Lean_Expr_hash(x_1);
x_158 = 32;
x_159 = lean_uint64_shift_right(x_157, x_158);
x_160 = lean_uint64_xor(x_157, x_159);
x_161 = 16;
x_162 = lean_uint64_shift_right(x_160, x_161);
x_163 = lean_uint64_xor(x_160, x_162);
x_164 = lean_uint64_to_usize(x_163);
x_165 = lean_usize_of_nat(x_156);
lean_dec(x_156);
x_166 = 1;
x_167 = lean_usize_sub(x_165, x_166);
x_168 = lean_usize_land(x_164, x_167);
x_169 = lean_array_uget(x_155, x_168);
lean_dec(x_155);
x_170 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__1___redArg(x_1, x_169);
lean_dec(x_169);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint64_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; lean_object* x_191; 
x_171 = lean_st_ref_get(x_2, x_154);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_box(0);
x_175 = lean_unsigned_to_nat(0u);
x_176 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_177 = lean_st_mk_ref(x_176, x_173);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_ctor_get(x_172, 0);
lean_inc(x_180);
lean_dec(x_172);
x_181 = lean_box(0);
x_182 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_183 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_184 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13;
x_185 = lean_box(0);
x_186 = lean_box(0);
x_187 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_187, 0, x_182);
lean_ctor_set(x_187, 1, x_174);
lean_ctor_set(x_187, 2, x_180);
lean_ctor_set(x_187, 3, x_184);
lean_ctor_set(x_187, 4, x_185);
lean_ctor_set(x_187, 5, x_175);
lean_ctor_set(x_187, 6, x_186);
lean_ctor_set_uint64(x_187, sizeof(void*)*7, x_183);
x_188 = lean_unbox(x_181);
lean_ctor_set_uint8(x_187, sizeof(void*)*7 + 8, x_188);
x_189 = lean_unbox(x_181);
lean_ctor_set_uint8(x_187, sizeof(void*)*7 + 9, x_189);
x_190 = lean_unbox(x_181);
lean_ctor_set_uint8(x_187, sizeof(void*)*7 + 10, x_190);
lean_inc(x_178);
lean_inc(x_1);
x_191 = l_Lean_Compiler_LCNF_toLCNFType(x_1, x_187, x_178, x_3, x_4, x_179);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_st_ref_get(x_178, x_193);
lean_dec(x_178);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_21 = x_192;
x_22 = x_195;
goto block_103;
}
else
{
lean_dec(x_178);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_191, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_191, 1);
lean_inc(x_197);
lean_dec(x_191);
x_21 = x_196;
x_22 = x_197;
goto block_103;
}
else
{
lean_dec(x_1);
return x_191;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_198 = lean_ctor_get(x_170, 0);
lean_inc(x_198);
lean_dec(x_170);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_154);
return x_199;
}
}
block_20:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_8);
lean_ctor_set(x_14, 4, x_9);
lean_ctor_set(x_14, 5, x_6);
x_15 = lean_st_ref_set(x_2, x_14, x_12);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_7);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
block_103:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_23 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(x_21, x_2, x_22);
lean_dec(x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_take(x_2, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_27, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_27, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 5);
lean_inc(x_34);
lean_dec(x_27);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; size_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; lean_object* x_51; uint8_t x_52; 
x_36 = lean_ctor_get(x_28, 0);
x_37 = lean_ctor_get(x_28, 1);
x_38 = lean_array_get_size(x_37);
x_39 = l_Lean_Expr_hash(x_1);
x_40 = 32;
x_41 = lean_uint64_shift_right(x_39, x_40);
x_42 = lean_uint64_xor(x_39, x_41);
x_43 = 16;
x_44 = lean_uint64_shift_right(x_42, x_43);
x_45 = lean_uint64_xor(x_42, x_44);
x_46 = lean_uint64_to_usize(x_45);
x_47 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_48 = 1;
x_49 = lean_usize_sub(x_47, x_48);
x_50 = lean_usize_land(x_46, x_49);
x_51 = lean_array_uget(x_37, x_50);
x_52 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_1, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_36, x_53);
lean_dec(x_36);
lean_inc(x_24);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_24);
lean_ctor_set(x_55, 2, x_51);
x_56 = lean_array_uset(x_37, x_50, x_55);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_mul(x_54, x_57);
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_div(x_58, x_59);
lean_dec(x_58);
x_61 = lean_array_get_size(x_56);
x_62 = lean_nat_dec_le(x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_56);
lean_ctor_set(x_28, 1, x_63);
lean_ctor_set(x_28, 0, x_54);
x_6 = x_34;
x_7 = x_24;
x_8 = x_32;
x_9 = x_33;
x_10 = x_31;
x_11 = x_30;
x_12 = x_29;
x_13 = x_28;
goto block_20;
}
else
{
lean_ctor_set(x_28, 1, x_56);
lean_ctor_set(x_28, 0, x_54);
x_6 = x_34;
x_7 = x_24;
x_8 = x_32;
x_9 = x_33;
x_10 = x_31;
x_11 = x_30;
x_12 = x_29;
x_13 = x_28;
goto block_20;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_box(0);
x_65 = lean_array_uset(x_37, x_50, x_64);
lean_inc(x_24);
x_66 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at___Lean_Compiler_SpecState_addEntry_spec__0_spec__0___redArg(x_1, x_24, x_51);
x_67 = lean_array_uset(x_65, x_50, x_66);
lean_ctor_set(x_28, 1, x_67);
x_6 = x_34;
x_7 = x_24;
x_8 = x_32;
x_9 = x_33;
x_10 = x_31;
x_11 = x_30;
x_12 = x_29;
x_13 = x_28;
goto block_20;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; size_t x_78; size_t x_79; size_t x_80; size_t x_81; size_t x_82; lean_object* x_83; uint8_t x_84; 
x_68 = lean_ctor_get(x_28, 0);
x_69 = lean_ctor_get(x_28, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_28);
x_70 = lean_array_get_size(x_69);
x_71 = l_Lean_Expr_hash(x_1);
x_72 = 32;
x_73 = lean_uint64_shift_right(x_71, x_72);
x_74 = lean_uint64_xor(x_71, x_73);
x_75 = 16;
x_76 = lean_uint64_shift_right(x_74, x_75);
x_77 = lean_uint64_xor(x_74, x_76);
x_78 = lean_uint64_to_usize(x_77);
x_79 = lean_usize_of_nat(x_70);
lean_dec(x_70);
x_80 = 1;
x_81 = lean_usize_sub(x_79, x_80);
x_82 = lean_usize_land(x_78, x_81);
x_83 = lean_array_uget(x_69, x_82);
x_84 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectMVars_visit_spec__0___redArg(x_1, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_add(x_68, x_85);
lean_dec(x_68);
lean_inc(x_24);
x_87 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_24);
lean_ctor_set(x_87, 2, x_83);
x_88 = lean_array_uset(x_69, x_82, x_87);
x_89 = lean_unsigned_to_nat(4u);
x_90 = lean_nat_mul(x_86, x_89);
x_91 = lean_unsigned_to_nat(3u);
x_92 = lean_nat_div(x_90, x_91);
lean_dec(x_90);
x_93 = lean_array_get_size(x_88);
x_94 = lean_nat_dec_le(x_92, x_93);
lean_dec(x_93);
lean_dec(x_92);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectMVars_visit_spec__1___redArg(x_88);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_86);
lean_ctor_set(x_96, 1, x_95);
x_6 = x_34;
x_7 = x_24;
x_8 = x_32;
x_9 = x_33;
x_10 = x_31;
x_11 = x_30;
x_12 = x_29;
x_13 = x_96;
goto block_20;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_86);
lean_ctor_set(x_97, 1, x_88);
x_6 = x_34;
x_7 = x_24;
x_8 = x_32;
x_9 = x_33;
x_10 = x_31;
x_11 = x_30;
x_12 = x_29;
x_13 = x_97;
goto block_20;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_box(0);
x_99 = lean_array_uset(x_69, x_82, x_98);
lean_inc(x_24);
x_100 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at___Lean_Compiler_SpecState_addEntry_spec__0_spec__0___redArg(x_1, x_24, x_83);
x_101 = lean_array_uset(x_99, x_82, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_68);
lean_ctor_set(x_102, 1, x_101);
x_6 = x_34;
x_7 = x_24;
x_8 = x_32;
x_9 = x_33;
x_10 = x_31;
x_11 = x_30;
x_12 = x_29;
x_13 = x_102;
goto block_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_1, x_2, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Name_hasMacroScopes(x_1);
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
lean_object* x_6; lean_object* x_7; 
x_6 = lean_erase_macro_scopes(x_1);
x_7 = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(x_6, x_2, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg(x_1, x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_12 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_2, x_3, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_2);
x_15 = lean_is_marked_borrowed(x_2);
lean_inc(x_10);
x_16 = l_Lean_Compiler_LCNF_mkParam(x_10, x_13, x_15, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_take(x_3, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
x_25 = lean_box(0);
x_26 = lean_box(0);
x_27 = lean_unbox(x_25);
x_28 = lean_unbox(x_26);
x_29 = l_Lean_LocalContext_mkLocalDecl(x_23, x_24, x_10, x_2, x_27, x_28);
lean_ctor_set(x_20, 0, x_29);
x_30 = lean_st_ref_set(x_3, x_20, x_21);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_17);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_17);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
x_37 = lean_ctor_get(x_20, 2);
x_38 = lean_ctor_get(x_20, 3);
x_39 = lean_ctor_get(x_20, 4);
x_40 = lean_ctor_get(x_20, 5);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_41 = lean_ctor_get(x_17, 0);
lean_inc(x_41);
x_42 = lean_box(0);
x_43 = lean_box(0);
x_44 = lean_unbox(x_42);
x_45 = lean_unbox(x_43);
x_46 = l_Lean_LocalContext_mkLocalDecl(x_35, x_41, x_10, x_2, x_44, x_45);
x_47 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_36);
lean_ctor_set(x_47, 2, x_37);
lean_ctor_set(x_47, 3, x_38);
lean_ctor_set(x_47, 4, x_39);
lean_ctor_set(x_47, 5, x_40);
x_48 = lean_st_ref_set(x_3, x_47, x_21);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_17);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_12);
if (x_52 == 0)
{
return x_12;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_12, 0);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_12);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_mkParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg(x_1, x_8, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_5, 0);
x_65 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___closed__0;
lean_inc(x_64);
lean_ctor_set_tag(x_12, 4);
lean_ctor_set(x_12, 1, x_65);
lean_ctor_set(x_12, 0, x_64);
x_16 = x_12;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
goto block_63;
}
else
{
lean_object* x_66; 
lean_free_object(x_12);
x_66 = lean_box(1);
x_16 = x_66;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
goto block_63;
}
block_63:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_inc(x_14);
x_22 = l_Lean_Compiler_LCNF_mkLetDecl(x_14, x_4, x_16, x_18, x_19, x_20, x_21, x_15);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_take(x_17, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 4);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
x_32 = lean_box(0);
x_33 = lean_box(0);
x_34 = lean_unbox(x_32);
x_35 = lean_unbox(x_33);
x_36 = l_Lean_LocalContext_mkLetDecl(x_29, x_31, x_14, x_2, x_3, x_34, x_35);
lean_inc(x_23);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_23);
x_38 = lean_array_push(x_30, x_37);
lean_ctor_set(x_26, 4, x_38);
lean_ctor_set(x_26, 0, x_36);
x_39 = lean_st_ref_set(x_17, x_26, x_27);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_23);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_44 = lean_ctor_get(x_26, 0);
x_45 = lean_ctor_get(x_26, 1);
x_46 = lean_ctor_get(x_26, 2);
x_47 = lean_ctor_get(x_26, 3);
x_48 = lean_ctor_get(x_26, 4);
x_49 = lean_ctor_get(x_26, 5);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_26);
x_50 = lean_ctor_get(x_23, 0);
lean_inc(x_50);
x_51 = lean_box(0);
x_52 = lean_box(0);
x_53 = lean_unbox(x_51);
x_54 = lean_unbox(x_52);
x_55 = l_Lean_LocalContext_mkLetDecl(x_44, x_50, x_14, x_2, x_3, x_53, x_54);
lean_inc(x_23);
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_23);
x_57 = lean_array_push(x_48, x_56);
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_45);
lean_ctor_set(x_58, 2, x_46);
lean_ctor_set(x_58, 3, x_47);
lean_ctor_set(x_58, 4, x_57);
lean_ctor_set(x_58, 5, x_49);
x_59 = lean_st_ref_set(x_17, x_58, x_27);
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
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_23);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_12, 0);
x_68 = lean_ctor_get(x_12, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_12);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_5, 0);
x_103 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___closed__0;
lean_inc(x_102);
x_104 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_69 = x_104;
x_70 = x_6;
x_71 = x_7;
x_72 = x_8;
x_73 = x_9;
x_74 = x_10;
goto block_101;
}
else
{
lean_object* x_105; 
x_105 = lean_box(1);
x_69 = x_105;
x_70 = x_6;
x_71 = x_7;
x_72 = x_8;
x_73 = x_9;
x_74 = x_10;
goto block_101;
}
block_101:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_inc(x_67);
x_75 = l_Lean_Compiler_LCNF_mkLetDecl(x_67, x_4, x_69, x_71, x_72, x_73, x_74, x_68);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_st_ref_take(x_70, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_79, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_79, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_79, 4);
lean_inc(x_85);
x_86 = lean_ctor_get(x_79, 5);
lean_inc(x_86);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 lean_ctor_release(x_79, 2);
 lean_ctor_release(x_79, 3);
 lean_ctor_release(x_79, 4);
 lean_ctor_release(x_79, 5);
 x_87 = x_79;
} else {
 lean_dec_ref(x_79);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_76, 0);
lean_inc(x_88);
x_89 = lean_box(0);
x_90 = lean_box(0);
x_91 = lean_unbox(x_89);
x_92 = lean_unbox(x_90);
x_93 = l_Lean_LocalContext_mkLetDecl(x_81, x_88, x_67, x_2, x_3, x_91, x_92);
lean_inc(x_76);
x_94 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_94, 0, x_76);
x_95 = lean_array_push(x_85, x_94);
if (lean_is_scalar(x_87)) {
 x_96 = lean_alloc_ctor(0, 6, 0);
} else {
 x_96 = x_87;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_82);
lean_ctor_set(x_96, 2, x_83);
lean_ctor_set(x_96, 3, x_84);
lean_ctor_set(x_96, 4, x_95);
lean_ctor_set(x_96, 5, x_86);
x_97 = lean_st_ref_set(x_70, x_96, x_80);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_76);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_expr_instantiate_rev(x_11, x_2);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_mkParam(x_10, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_15);
x_17 = l_Lean_Compiler_LCNF_Param_toExpr(x_15);
x_18 = lean_array_push(x_2, x_17);
x_19 = lean_array_push(x_3, x_15);
x_1 = x_12;
x_2 = x_18;
x_3 = x_19;
x_9 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_8);
lean_dec(x_7);
x_25 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_visitLambda___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda___closed__0;
x_9 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go(x_1, x_8, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_2, x_11);
if (x_12 == 0)
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_expr_instantiate_rev(x_14, x_3);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_mkParam(x_13, x_16, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_2, x_20);
lean_dec(x_2);
lean_inc(x_18);
x_22 = l_Lean_Compiler_LCNF_Param_toExpr(x_18);
x_23 = lean_array_push(x_3, x_22);
x_24 = lean_array_push(x_4, x_18);
x_1 = x_15;
x_2 = x_21;
x_3 = x_23;
x_4 = x_24;
x_10 = x_19;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_30 = lean_expr_instantiate_rev(x_1, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_10);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_33 = lean_expr_instantiate_rev(x_1, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_10);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda___closed__0;
x_10 = l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go(x_1, x_2, x_9, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ndrec", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; uint8_t x_5; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
lean_inc(x_4);
lean_inc(x_1);
x_15 = l_Lean_Environment_find_x3f(x_1, x_4, x_14);
if (lean_obj_tag(x_15) == 0)
{
goto block_12;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
switch (lean_obj_tag(x_16)) {
case 4:
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_1);
x_17 = lean_box(1);
x_18 = lean_unbox(x_17);
return x_18;
}
case 6:
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_1);
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
return x_20;
}
case 7:
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_1);
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
return x_22;
}
default: 
{
lean_dec(x_16);
goto block_12;
}
}
}
block_9:
{
if (x_5 == 0)
{
uint8_t x_6; 
lean_inc(x_4);
x_6 = l_Lean_Environment_isProjectionFn(x_1, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2;
x_8 = lean_name_eq(x_4, x_7);
lean_dec(x_4);
return x_8;
}
else
{
lean_dec(x_4);
return x_6;
}
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
block_12:
{
uint8_t x_10; 
lean_inc(x_4);
lean_inc(x_1);
x_10 = l_Lean_isCasesOnRecursor(x_1, x_4);
if (x_10 == 0)
{
uint8_t x_11; 
lean_inc(x_4);
lean_inc(x_1);
x_11 = lean_is_no_confusion(x_1, x_4);
x_5 = x_11;
goto block_9;
}
else
{
x_5 = x_10;
goto block_9;
}
}
}
else
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = l_Lean_mkAppN(x_1, x_4);
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
x_14 = l_Lean_Meta_mkLambdaFVars(x_4, x_11, x_2, x_3, x_2, x_13, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint64_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_9 = lean_st_ref_get(x_3, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_14 = lean_st_mk_ref(x_13, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_box(1);
x_28 = lean_box(1);
x_29 = lean_box(0);
x_30 = lean_box(2);
x_31 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_31, 0, x_8);
lean_ctor_set_uint8(x_31, 1, x_8);
lean_ctor_set_uint8(x_31, 2, x_8);
lean_ctor_set_uint8(x_31, 3, x_8);
lean_ctor_set_uint8(x_31, 4, x_8);
x_32 = lean_unbox(x_27);
lean_ctor_set_uint8(x_31, 5, x_32);
x_33 = lean_unbox(x_27);
lean_ctor_set_uint8(x_31, 6, x_33);
lean_ctor_set_uint8(x_31, 7, x_8);
x_34 = lean_unbox(x_27);
lean_ctor_set_uint8(x_31, 8, x_34);
x_35 = lean_unbox(x_28);
lean_ctor_set_uint8(x_31, 9, x_35);
x_36 = lean_unbox(x_29);
lean_ctor_set_uint8(x_31, 10, x_36);
x_37 = lean_unbox(x_27);
lean_ctor_set_uint8(x_31, 11, x_37);
x_38 = lean_unbox(x_27);
lean_ctor_set_uint8(x_31, 12, x_38);
x_39 = lean_unbox(x_27);
lean_ctor_set_uint8(x_31, 13, x_39);
x_40 = lean_unbox(x_30);
lean_ctor_set_uint8(x_31, 14, x_40);
x_41 = lean_unbox(x_27);
lean_ctor_set_uint8(x_31, 15, x_41);
x_42 = lean_unbox(x_27);
lean_ctor_set_uint8(x_31, 16, x_42);
x_43 = lean_unbox(x_27);
lean_ctor_set_uint8(x_31, 17, x_43);
x_44 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_31);
x_45 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13;
x_46 = lean_box(0);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_48, 0, x_31);
lean_ctor_set(x_48, 1, x_12);
lean_ctor_set(x_48, 2, x_26);
lean_ctor_set(x_48, 3, x_45);
lean_ctor_set(x_48, 4, x_46);
lean_ctor_set(x_48, 5, x_7);
lean_ctor_set(x_48, 6, x_47);
lean_ctor_set_uint64(x_48, sizeof(void*)*7, x_44);
lean_ctor_set_uint8(x_48, sizeof(void*)*7 + 8, x_8);
lean_ctor_set_uint8(x_48, sizeof(void*)*7 + 9, x_8);
lean_ctor_set_uint8(x_48, sizeof(void*)*7 + 10, x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_15);
lean_inc(x_48);
lean_inc(x_1);
x_49 = lean_infer_type(x_1, x_48, x_15, x_4, x_5, x_16);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_box(x_8);
x_53 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0___boxed), 10, 3);
lean_closure_set(x_53, 0, x_1);
lean_closure_set(x_53, 1, x_52);
lean_closure_set(x_53, 2, x_27);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_2);
lean_inc(x_15);
x_55 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_50, x_54, x_53, x_8, x_8, x_48, x_15, x_4, x_5, x_51);
x_17 = x_55;
goto block_25;
}
else
{
lean_dec(x_48);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_17 = x_49;
goto block_25;
}
block_25:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_15, x_19);
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_dec(x_15);
return x_17;
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_6);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_1, x_2, x_3, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_6 = l_Lean_BinderInfo_isImplicit(x_5);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_7; uint8_t x_8; uint8_t x_19; 
lean_inc(x_4);
x_7 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit(x_4);
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_7, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_eq(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_dec(x_31);
goto block_29;
}
else
{
uint8_t x_35; 
x_35 = lean_expr_has_loose_bvar(x_31, x_33);
if (x_35 == 0)
{
if (x_6 == 0)
{
lean_dec(x_31);
goto block_18;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_expr_lower_loose_bvars(x_31, x_36, x_36);
lean_dec(x_31);
return x_37;
}
}
else
{
lean_dec(x_31);
goto block_18;
}
}
}
else
{
lean_dec(x_30);
goto block_29;
}
}
else
{
goto block_29;
}
block_12:
{
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_5, x_5);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_11;
}
else
{
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
block_18:
{
size_t x_13; uint8_t x_14; 
x_13 = lean_ptr_addr(x_3);
x_14 = lean_usize_dec_eq(x_13, x_13);
if (x_14 == 0)
{
lean_dec(x_4);
x_8 = x_14;
goto block_12;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_16 = lean_ptr_addr(x_7);
x_17 = lean_usize_dec_eq(x_15, x_16);
x_8 = x_17;
goto block_12;
}
}
block_23:
{
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_1);
x_20 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_5, x_5);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_22;
}
else
{
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
block_29:
{
size_t x_24; uint8_t x_25; 
x_24 = lean_ptr_addr(x_3);
x_25 = lean_usize_dec_eq(x_24, x_24);
if (x_25 == 0)
{
lean_dec(x_4);
x_19 = x_25;
goto block_23;
}
else
{
size_t x_26; size_t x_27; uint8_t x_28; 
x_26 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_27 = lean_ptr_addr(x_7);
x_28 = lean_usize_dec_eq(x_26, x_27);
x_19 = x_28;
goto block_23;
}
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_litToValue(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_litToValue(x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
x_11 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_2, x_7);
if (x_8 == 1)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_2, x_10);
lean_dec(x_2);
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(x_12);
x_15 = lean_expr_instantiate1(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_1 = x_15;
x_2 = x_11;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_nat_add(x_11, x_10);
lean_dec(x_11);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_17);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_1, x_17, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_1 = x_19;
x_2 = x_17;
x_6 = x_20;
goto _start;
}
else
{
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg(x_1, x_2, x_3, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__0;
x_9 = l_ReaderT_instMonad___redArg(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_ctor_get(x_11, 3);
x_17 = lean_ctor_get(x_11, 4);
x_18 = lean_ctor_get(x_11, 1);
lean_dec(x_18);
x_19 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__1;
x_20 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__2;
lean_inc(x_14);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_21, 0, x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_17);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_16);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_26, 0, x_15);
lean_ctor_set(x_11, 4, x_24);
lean_ctor_set(x_11, 3, x_25);
lean_ctor_set(x_11, 2, x_26);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_11, 0, x_23);
lean_ctor_set(x_9, 1, x_20);
x_27 = l_ReaderT_instMonad___redArg(x_9);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 2);
x_34 = lean_ctor_get(x_29, 3);
x_35 = lean_ctor_get(x_29, 4);
x_36 = lean_ctor_get(x_29, 1);
lean_dec(x_36);
x_37 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__3;
x_38 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__4;
lean_inc(x_32);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_39, 0, x_32);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_40, 0, x_32);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_35);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_34);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_44, 0, x_33);
lean_ctor_set(x_29, 4, x_42);
lean_ctor_set(x_29, 3, x_43);
lean_ctor_set(x_29, 2, x_44);
lean_ctor_set(x_29, 1, x_37);
lean_ctor_set(x_29, 0, x_41);
lean_ctor_set(x_27, 1, x_38);
x_45 = l_ReaderT_instMonad___redArg(x_27);
x_46 = lean_box(0);
x_47 = l_instInhabitedOfMonad___redArg(x_45, x_46);
x_48 = lean_panic_fn(x_47, x_1);
x_49 = lean_apply_6(x_48, x_2, x_3, x_4, x_5, x_6, x_7);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_50 = lean_ctor_get(x_29, 0);
x_51 = lean_ctor_get(x_29, 2);
x_52 = lean_ctor_get(x_29, 3);
x_53 = lean_ctor_get(x_29, 4);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_29);
x_54 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__3;
x_55 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__4;
lean_inc(x_50);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_56, 0, x_50);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_57, 0, x_50);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_53);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_60, 0, x_52);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_61, 0, x_51);
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_60);
lean_ctor_set(x_62, 4, x_59);
lean_ctor_set(x_27, 1, x_55);
lean_ctor_set(x_27, 0, x_62);
x_63 = l_ReaderT_instMonad___redArg(x_27);
x_64 = lean_box(0);
x_65 = l_instInhabitedOfMonad___redArg(x_63, x_64);
x_66 = lean_panic_fn(x_65, x_1);
x_67 = lean_apply_6(x_66, x_2, x_3, x_4, x_5, x_6, x_7);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_68 = lean_ctor_get(x_27, 0);
lean_inc(x_68);
lean_dec(x_27);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_68, 4);
lean_inc(x_72);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 lean_ctor_release(x_68, 2);
 lean_ctor_release(x_68, 3);
 lean_ctor_release(x_68, 4);
 x_73 = x_68;
} else {
 lean_dec_ref(x_68);
 x_73 = lean_box(0);
}
x_74 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__3;
x_75 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__4;
lean_inc(x_69);
x_76 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_76, 0, x_69);
x_77 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_77, 0, x_69);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_79, 0, x_72);
x_80 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_80, 0, x_71);
x_81 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_81, 0, x_70);
if (lean_is_scalar(x_73)) {
 x_82 = lean_alloc_ctor(0, 5, 0);
} else {
 x_82 = x_73;
}
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_80);
lean_ctor_set(x_82, 4, x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_75);
x_84 = l_ReaderT_instMonad___redArg(x_83);
x_85 = lean_box(0);
x_86 = l_instInhabitedOfMonad___redArg(x_84, x_85);
x_87 = lean_panic_fn(x_86, x_1);
x_88 = lean_apply_6(x_87, x_2, x_3, x_4, x_5, x_6, x_7);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_89 = lean_ctor_get(x_11, 0);
x_90 = lean_ctor_get(x_11, 2);
x_91 = lean_ctor_get(x_11, 3);
x_92 = lean_ctor_get(x_11, 4);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_11);
x_93 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__1;
x_94 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__2;
lean_inc(x_89);
x_95 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_95, 0, x_89);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_96, 0, x_89);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_98, 0, x_92);
x_99 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_99, 0, x_91);
x_100 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_100, 0, x_90);
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_93);
lean_ctor_set(x_101, 2, x_100);
lean_ctor_set(x_101, 3, x_99);
lean_ctor_set(x_101, 4, x_98);
lean_ctor_set(x_9, 1, x_94);
lean_ctor_set(x_9, 0, x_101);
x_102 = l_ReaderT_instMonad___redArg(x_9);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_103, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 4);
lean_inc(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 lean_ctor_release(x_103, 2);
 lean_ctor_release(x_103, 3);
 lean_ctor_release(x_103, 4);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
x_110 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__3;
x_111 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__4;
lean_inc(x_105);
x_112 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_112, 0, x_105);
x_113 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_113, 0, x_105);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_115, 0, x_108);
x_116 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_116, 0, x_107);
x_117 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_117, 0, x_106);
if (lean_is_scalar(x_109)) {
 x_118 = lean_alloc_ctor(0, 5, 0);
} else {
 x_118 = x_109;
}
lean_ctor_set(x_118, 0, x_114);
lean_ctor_set(x_118, 1, x_110);
lean_ctor_set(x_118, 2, x_117);
lean_ctor_set(x_118, 3, x_116);
lean_ctor_set(x_118, 4, x_115);
if (lean_is_scalar(x_104)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_104;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_111);
x_120 = l_ReaderT_instMonad___redArg(x_119);
x_121 = lean_box(0);
x_122 = l_instInhabitedOfMonad___redArg(x_120, x_121);
x_123 = lean_panic_fn(x_122, x_1);
x_124 = lean_apply_6(x_123, x_2, x_3, x_4, x_5, x_6, x_7);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_125 = lean_ctor_get(x_9, 0);
lean_inc(x_125);
lean_dec(x_9);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 3);
lean_inc(x_128);
x_129 = lean_ctor_get(x_125, 4);
lean_inc(x_129);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 lean_ctor_release(x_125, 3);
 lean_ctor_release(x_125, 4);
 x_130 = x_125;
} else {
 lean_dec_ref(x_125);
 x_130 = lean_box(0);
}
x_131 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__1;
x_132 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__2;
lean_inc(x_126);
x_133 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_133, 0, x_126);
x_134 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_134, 0, x_126);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_136, 0, x_129);
x_137 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_137, 0, x_128);
x_138 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_138, 0, x_127);
if (lean_is_scalar(x_130)) {
 x_139 = lean_alloc_ctor(0, 5, 0);
} else {
 x_139 = x_130;
}
lean_ctor_set(x_139, 0, x_135);
lean_ctor_set(x_139, 1, x_131);
lean_ctor_set(x_139, 2, x_138);
lean_ctor_set(x_139, 3, x_137);
lean_ctor_set(x_139, 4, x_136);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_132);
x_141 = l_ReaderT_instMonad___redArg(x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_142, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_142, 4);
lean_inc(x_147);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 lean_ctor_release(x_142, 4);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__3;
x_150 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__4;
lean_inc(x_144);
x_151 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_151, 0, x_144);
x_152 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_152, 0, x_144);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_154, 0, x_147);
x_155 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_155, 0, x_146);
x_156 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_156, 0, x_145);
if (lean_is_scalar(x_148)) {
 x_157 = lean_alloc_ctor(0, 5, 0);
} else {
 x_157 = x_148;
}
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_149);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set(x_157, 3, x_155);
lean_ctor_set(x_157, 4, x_154);
if (lean_is_scalar(x_143)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_143;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_150);
x_159 = l_ReaderT_instMonad___redArg(x_158);
x_160 = lean_box(0);
x_161 = l_instInhabitedOfMonad___redArg(x_159, x_160);
x_162 = lean_panic_fn(x_161, x_1);
x_163 = lean_apply_6(x_162, x_2, x_3, x_4, x_5, x_6, x_7);
return x_163;
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information", 157, 157);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__5;
x_2 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__2;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__6;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg(x_2, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitCore", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__2;
x_2 = lean_unsigned_to_nat(57u);
x_3 = lean_unsigned_to_nat(435u);
x_4 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__1;
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_35; 
x_35 = !lean_is_exclusive(x_5);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_36 = lean_ctor_get(x_5, 0);
x_37 = lean_ctor_get(x_5, 1);
x_38 = lean_ctor_get(x_5, 2);
x_39 = lean_ctor_get(x_5, 3);
x_40 = lean_ctor_get(x_5, 4);
x_41 = lean_ctor_get(x_5, 5);
x_42 = lean_ctor_get(x_5, 6);
x_43 = lean_ctor_get(x_5, 7);
x_44 = lean_ctor_get(x_5, 8);
x_45 = lean_ctor_get(x_5, 9);
x_46 = lean_ctor_get(x_5, 10);
x_47 = lean_ctor_get(x_5, 11);
x_48 = lean_ctor_get(x_5, 12);
x_49 = lean_nat_dec_eq(x_39, x_40);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_st_ref_get(x_2, x_7);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_1);
x_55 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__0___redArg(x_54, x_1);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_free_object(x_50);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_39, x_56);
lean_dec(x_39);
lean_ctor_set(x_5, 3, x_57);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_64; lean_object* x_65; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
x_59 = lean_st_ref_get(x_2, x_53);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_64 = lean_ctor_get(x_60, 5);
lean_inc(x_64);
lean_dec(x_60);
x_65 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_64, x_58);
lean_dec(x_64);
if (lean_obj_tag(x_65) == 0)
{
if (x_49 == 0)
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_58);
x_8 = x_66;
x_9 = x_2;
x_10 = x_61;
goto block_34;
}
else
{
lean_dec(x_58);
goto block_63;
}
}
else
{
lean_dec(x_65);
lean_dec(x_58);
goto block_63;
}
block_63:
{
lean_object* x_62; 
x_62 = lean_box(0);
x_8 = x_62;
x_9 = x_2;
x_10 = x_61;
goto block_34;
}
}
case 4:
{
lean_object* x_67; 
lean_inc(x_2);
lean_inc(x_1);
x_67 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_2, x_3, x_4, x_5, x_6, x_53);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_8 = x_68;
x_9 = x_2;
x_10 = x_69;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_67;
}
}
case 5:
{
lean_object* x_70; 
lean_inc(x_2);
lean_inc(x_1);
x_70 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_2, x_3, x_4, x_5, x_6, x_53);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_8 = x_71;
x_9 = x_2;
x_10 = x_72;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_70;
}
}
case 6:
{
lean_object* x_73; 
lean_inc(x_2);
lean_inc(x_1);
x_73 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(x_1, x_2, x_3, x_4, x_5, x_6, x_53);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_8 = x_74;
x_9 = x_2;
x_10 = x_75;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_73;
}
}
case 8:
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda___closed__0;
lean_inc(x_2);
lean_inc(x_1);
x_77 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(x_1, x_76, x_2, x_3, x_4, x_5, x_6, x_53);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_8 = x_78;
x_9 = x_2;
x_10 = x_79;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_77;
}
}
case 9:
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_1, 0);
lean_inc(x_80);
x_81 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(x_80, x_2, x_3, x_4, x_5, x_6, x_53);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_8 = x_82;
x_9 = x_2;
x_10 = x_83;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_81;
}
}
case 10:
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_1, 1);
lean_inc(x_84);
lean_inc(x_2);
x_85 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(x_84, x_2, x_3, x_4, x_5, x_6, x_53);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_8 = x_86;
x_9 = x_2;
x_10 = x_87;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_85;
}
}
case 11:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_1, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_1, 2);
lean_inc(x_90);
lean_inc(x_2);
x_91 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(x_88, x_89, x_90, x_2, x_3, x_4, x_5, x_6, x_53);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_8 = x_92;
x_9 = x_2;
x_10 = x_93;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_91;
}
}
default: 
{
lean_object* x_94; lean_object* x_95; 
x_94 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__3;
lean_inc(x_2);
x_95 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_94, x_2, x_3, x_4, x_5, x_6, x_53);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_8 = x_96;
x_9 = x_2;
x_10 = x_97;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_95;
}
}
}
}
else
{
lean_object* x_98; 
lean_free_object(x_5);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = lean_ctor_get(x_55, 0);
lean_inc(x_98);
lean_dec(x_55);
lean_ctor_set(x_50, 0, x_98);
return x_50;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_50, 0);
x_100 = lean_ctor_get(x_50, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_50);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
lean_inc(x_1);
x_102 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__0___redArg(x_101, x_1);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_add(x_39, x_103);
lean_dec(x_39);
lean_ctor_set(x_5, 3, x_104);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_111; lean_object* x_112; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_105 = lean_ctor_get(x_1, 0);
lean_inc(x_105);
x_106 = lean_st_ref_get(x_2, x_100);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_111 = lean_ctor_get(x_107, 5);
lean_inc(x_111);
lean_dec(x_107);
x_112 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_111, x_105);
lean_dec(x_111);
if (lean_obj_tag(x_112) == 0)
{
if (x_49 == 0)
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_105);
x_8 = x_113;
x_9 = x_2;
x_10 = x_108;
goto block_34;
}
else
{
lean_dec(x_105);
goto block_110;
}
}
else
{
lean_dec(x_112);
lean_dec(x_105);
goto block_110;
}
block_110:
{
lean_object* x_109; 
x_109 = lean_box(0);
x_8 = x_109;
x_9 = x_2;
x_10 = x_108;
goto block_34;
}
}
case 4:
{
lean_object* x_114; 
lean_inc(x_2);
lean_inc(x_1);
x_114 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_2, x_3, x_4, x_5, x_6, x_100);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_8 = x_115;
x_9 = x_2;
x_10 = x_116;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_114;
}
}
case 5:
{
lean_object* x_117; 
lean_inc(x_2);
lean_inc(x_1);
x_117 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_2, x_3, x_4, x_5, x_6, x_100);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_8 = x_118;
x_9 = x_2;
x_10 = x_119;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_117;
}
}
case 6:
{
lean_object* x_120; 
lean_inc(x_2);
lean_inc(x_1);
x_120 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(x_1, x_2, x_3, x_4, x_5, x_6, x_100);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_8 = x_121;
x_9 = x_2;
x_10 = x_122;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_120;
}
}
case 8:
{
lean_object* x_123; lean_object* x_124; 
x_123 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda___closed__0;
lean_inc(x_2);
lean_inc(x_1);
x_124 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(x_1, x_123, x_2, x_3, x_4, x_5, x_6, x_100);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_8 = x_125;
x_9 = x_2;
x_10 = x_126;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_124;
}
}
case 9:
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_1, 0);
lean_inc(x_127);
x_128 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(x_127, x_2, x_3, x_4, x_5, x_6, x_100);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_8 = x_129;
x_9 = x_2;
x_10 = x_130;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_128;
}
}
case 10:
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_1, 1);
lean_inc(x_131);
lean_inc(x_2);
x_132 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(x_131, x_2, x_3, x_4, x_5, x_6, x_100);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_8 = x_133;
x_9 = x_2;
x_10 = x_134;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_132;
}
}
case 11:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_1, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_1, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_1, 2);
lean_inc(x_137);
lean_inc(x_2);
x_138 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(x_135, x_136, x_137, x_2, x_3, x_4, x_5, x_6, x_100);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_8 = x_139;
x_9 = x_2;
x_10 = x_140;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_138;
}
}
default: 
{
lean_object* x_141; lean_object* x_142; 
x_141 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__3;
lean_inc(x_2);
x_142 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_141, x_2, x_3, x_4, x_5, x_6, x_100);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_8 = x_143;
x_9 = x_2;
x_10 = x_144;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_142;
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_free_object(x_5);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lean_ctor_get(x_102, 0);
lean_inc(x_145);
lean_dec(x_102);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_100);
return x_146;
}
}
}
else
{
lean_object* x_147; 
lean_free_object(x_5);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_147 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg(x_41, x_7);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; uint8_t x_163; 
x_148 = lean_ctor_get(x_5, 0);
x_149 = lean_ctor_get(x_5, 1);
x_150 = lean_ctor_get(x_5, 2);
x_151 = lean_ctor_get(x_5, 3);
x_152 = lean_ctor_get(x_5, 4);
x_153 = lean_ctor_get(x_5, 5);
x_154 = lean_ctor_get(x_5, 6);
x_155 = lean_ctor_get(x_5, 7);
x_156 = lean_ctor_get(x_5, 8);
x_157 = lean_ctor_get(x_5, 9);
x_158 = lean_ctor_get(x_5, 10);
x_159 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_160 = lean_ctor_get(x_5, 11);
x_161 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_162 = lean_ctor_get(x_5, 12);
lean_inc(x_162);
lean_inc(x_160);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_5);
x_163 = lean_nat_dec_eq(x_151, x_152);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_164 = lean_st_ref_get(x_2, x_7);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_167 = x_164;
} else {
 lean_dec_ref(x_164);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_dec(x_165);
lean_inc(x_1);
x_169 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0_spec__0___redArg(x_168, x_1);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_167);
x_170 = lean_unsigned_to_nat(1u);
x_171 = lean_nat_add(x_151, x_170);
lean_dec(x_151);
x_172 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_172, 0, x_148);
lean_ctor_set(x_172, 1, x_149);
lean_ctor_set(x_172, 2, x_150);
lean_ctor_set(x_172, 3, x_171);
lean_ctor_set(x_172, 4, x_152);
lean_ctor_set(x_172, 5, x_153);
lean_ctor_set(x_172, 6, x_154);
lean_ctor_set(x_172, 7, x_155);
lean_ctor_set(x_172, 8, x_156);
lean_ctor_set(x_172, 9, x_157);
lean_ctor_set(x_172, 10, x_158);
lean_ctor_set(x_172, 11, x_160);
lean_ctor_set(x_172, 12, x_162);
lean_ctor_set_uint8(x_172, sizeof(void*)*13, x_159);
lean_ctor_set_uint8(x_172, sizeof(void*)*13 + 1, x_161);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_179; lean_object* x_180; 
lean_dec(x_172);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_173 = lean_ctor_get(x_1, 0);
lean_inc(x_173);
x_174 = lean_st_ref_get(x_2, x_166);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_179 = lean_ctor_get(x_175, 5);
lean_inc(x_179);
lean_dec(x_175);
x_180 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_179, x_173);
lean_dec(x_179);
if (lean_obj_tag(x_180) == 0)
{
if (x_163 == 0)
{
lean_object* x_181; 
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_173);
x_8 = x_181;
x_9 = x_2;
x_10 = x_176;
goto block_34;
}
else
{
lean_dec(x_173);
goto block_178;
}
}
else
{
lean_dec(x_180);
lean_dec(x_173);
goto block_178;
}
block_178:
{
lean_object* x_177; 
x_177 = lean_box(0);
x_8 = x_177;
x_9 = x_2;
x_10 = x_176;
goto block_34;
}
}
case 4:
{
lean_object* x_182; 
lean_inc(x_2);
lean_inc(x_1);
x_182 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_2, x_3, x_4, x_172, x_6, x_166);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_8 = x_183;
x_9 = x_2;
x_10 = x_184;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_182;
}
}
case 5:
{
lean_object* x_185; 
lean_inc(x_2);
lean_inc(x_1);
x_185 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_2, x_3, x_4, x_172, x_6, x_166);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_8 = x_186;
x_9 = x_2;
x_10 = x_187;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_185;
}
}
case 6:
{
lean_object* x_188; 
lean_inc(x_2);
lean_inc(x_1);
x_188 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(x_1, x_2, x_3, x_4, x_172, x_6, x_166);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_8 = x_189;
x_9 = x_2;
x_10 = x_190;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_188;
}
}
case 8:
{
lean_object* x_191; lean_object* x_192; 
x_191 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda___closed__0;
lean_inc(x_2);
lean_inc(x_1);
x_192 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(x_1, x_191, x_2, x_3, x_4, x_172, x_6, x_166);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_8 = x_193;
x_9 = x_2;
x_10 = x_194;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_192;
}
}
case 9:
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_1, 0);
lean_inc(x_195);
x_196 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(x_195, x_2, x_3, x_4, x_172, x_6, x_166);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_8 = x_197;
x_9 = x_2;
x_10 = x_198;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_196;
}
}
case 10:
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_1, 1);
lean_inc(x_199);
lean_inc(x_2);
x_200 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(x_199, x_2, x_3, x_4, x_172, x_6, x_166);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_8 = x_201;
x_9 = x_2;
x_10 = x_202;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_200;
}
}
case 11:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_203 = lean_ctor_get(x_1, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_1, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_1, 2);
lean_inc(x_205);
lean_inc(x_2);
x_206 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(x_203, x_204, x_205, x_2, x_3, x_4, x_172, x_6, x_166);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_8 = x_207;
x_9 = x_2;
x_10 = x_208;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_206;
}
}
default: 
{
lean_object* x_209; lean_object* x_210; 
x_209 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__3;
lean_inc(x_2);
x_210 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_209, x_2, x_3, x_4, x_172, x_6, x_166);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_8 = x_211;
x_9 = x_2;
x_10 = x_212;
goto block_34;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_210;
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_162);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_213 = lean_ctor_get(x_169, 0);
lean_inc(x_213);
lean_dec(x_169);
if (lean_is_scalar(x_167)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_167;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_166);
return x_214;
}
}
else
{
lean_object* x_215; 
lean_dec(x_162);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_215 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg(x_153, x_7);
return x_215;
}
}
block_34:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_take(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_8);
x_16 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_15, x_1, x_8);
lean_ctor_set(x_12, 1, x_16);
x_17 = lean_st_ref_set(x_9, x_12, x_13);
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_8);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
x_24 = lean_ctor_get(x_12, 2);
x_25 = lean_ctor_get(x_12, 3);
x_26 = lean_ctor_get(x_12, 4);
x_27 = lean_ctor_get(x_12, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
lean_inc(x_8);
x_28 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_23, x_1, x_8);
x_29 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
lean_ctor_set(x_29, 5, x_27);
x_30 = lean_st_ref_set(x_9, x_29, x_13);
lean_dec(x_9);
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
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_29; lean_object* x_30; lean_object* x_58; lean_object* x_59; uint64_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_st_ref_get(x_3, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_19 = lean_st_mk_ref(x_18, x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_expr_instantiate_rev(x_10, x_2);
lean_dec(x_10);
x_24 = lean_expr_instantiate_rev(x_11, x_2);
lean_dec(x_11);
x_58 = lean_box(0);
x_59 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_60 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_61 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13;
x_62 = lean_box(0);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_16);
lean_ctor_set(x_64, 2, x_22);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_62);
lean_ctor_set(x_64, 5, x_17);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set_uint64(x_64, sizeof(void*)*7, x_60);
x_65 = lean_unbox(x_58);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 8, x_65);
x_66 = lean_unbox(x_58);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 9, x_66);
x_67 = lean_unbox(x_58);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 10, x_67);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_20);
lean_inc(x_23);
x_68 = l_Lean_Meta_isProp(x_23, x_64, x_20, x_6, x_7, x_21);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_st_ref_get(x_20, x_70);
lean_dec(x_20);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_unbox(x_69);
lean_dec(x_69);
x_29 = x_73;
x_30 = x_72;
goto block_57;
}
else
{
lean_dec(x_20);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_dec(x_68);
x_76 = lean_unbox(x_74);
lean_dec(x_74);
x_29 = x_76;
x_30 = x_75;
goto block_57;
}
else
{
uint8_t x_77; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_68);
if (x_77 == 0)
{
return x_68;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_68, 0);
x_79 = lean_ctor_get(x_68, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_68);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
block_28:
{
lean_object* x_26; 
x_26 = lean_array_push(x_2, x_24);
x_1 = x_12;
x_2 = x_26;
x_8 = x_25;
goto _start;
}
block_57:
{
if (x_29 == 0)
{
lean_object* x_31; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_23);
x_31 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_23, x_3, x_6, x_7, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_23);
x_35 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_23, x_3, x_6, x_7, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_24);
x_38 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_24, x_3, x_4, x_5, x_6, x_7, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(x_9, x_23, x_24, x_36, x_39, x_3, x_4, x_5, x_6, x_7, x_40);
lean_dec(x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Expr_fvar___override(x_44);
x_46 = lean_array_push(x_2, x_45);
x_1 = x_12;
x_2 = x_46;
x_8 = x_43;
goto _start;
}
else
{
lean_dec(x_36);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_38;
}
}
else
{
uint8_t x_48; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_35);
if (x_48 == 0)
{
return x_35;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_35, 0);
x_50 = lean_ctor_get(x_35, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_35);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; 
lean_dec(x_23);
lean_dec(x_9);
x_52 = lean_ctor_get(x_31, 1);
lean_inc(x_52);
lean_dec(x_31);
x_25 = x_52;
goto block_28;
}
}
else
{
uint8_t x_53; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_31);
if (x_53 == 0)
{
return x_31;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_31, 0);
x_55 = lean_ctor_get(x_31, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_31);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_dec(x_23);
lean_dec(x_9);
x_25 = x_30;
goto block_28;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_82 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_81, x_3, x_4, x_5, x_6, x_7, x_8);
return x_82;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_80; 
x_80 = !lean_is_exclusive(x_5);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_81 = lean_ctor_get(x_5, 0);
x_82 = lean_ctor_get(x_5, 1);
x_83 = lean_ctor_get(x_5, 2);
x_84 = lean_ctor_get(x_5, 3);
x_85 = lean_ctor_get(x_5, 4);
x_86 = lean_ctor_get(x_5, 5);
x_87 = lean_ctor_get(x_5, 6);
x_88 = lean_ctor_get(x_5, 7);
x_89 = lean_ctor_get(x_5, 8);
x_90 = lean_ctor_get(x_5, 9);
x_91 = lean_ctor_get(x_5, 10);
x_92 = lean_ctor_get(x_5, 11);
x_93 = lean_ctor_get(x_5, 12);
x_94 = lean_nat_dec_eq(x_84, x_85);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof(x_1);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint64_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_96 = lean_st_ref_get(x_2, x_7);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_box(0);
x_100 = lean_unsigned_to_nat(0u);
x_101 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_102 = lean_st_mk_ref(x_101, x_98);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_97, 0);
lean_inc(x_105);
lean_dec(x_97);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_add(x_84, x_106);
lean_dec(x_84);
lean_ctor_set(x_5, 3, x_107);
x_108 = lean_box(1);
x_109 = lean_box(1);
x_110 = lean_box(0);
x_111 = lean_box(2);
x_112 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_112, 0, x_94);
lean_ctor_set_uint8(x_112, 1, x_94);
lean_ctor_set_uint8(x_112, 2, x_94);
lean_ctor_set_uint8(x_112, 3, x_94);
lean_ctor_set_uint8(x_112, 4, x_94);
x_113 = lean_unbox(x_108);
lean_ctor_set_uint8(x_112, 5, x_113);
x_114 = lean_unbox(x_108);
lean_ctor_set_uint8(x_112, 6, x_114);
lean_ctor_set_uint8(x_112, 7, x_94);
x_115 = lean_unbox(x_108);
lean_ctor_set_uint8(x_112, 8, x_115);
x_116 = lean_unbox(x_109);
lean_ctor_set_uint8(x_112, 9, x_116);
x_117 = lean_unbox(x_110);
lean_ctor_set_uint8(x_112, 10, x_117);
x_118 = lean_unbox(x_108);
lean_ctor_set_uint8(x_112, 11, x_118);
x_119 = lean_unbox(x_108);
lean_ctor_set_uint8(x_112, 12, x_119);
x_120 = lean_unbox(x_108);
lean_ctor_set_uint8(x_112, 13, x_120);
x_121 = lean_unbox(x_111);
lean_ctor_set_uint8(x_112, 14, x_121);
x_122 = lean_unbox(x_108);
lean_ctor_set_uint8(x_112, 15, x_122);
x_123 = lean_unbox(x_108);
lean_ctor_set_uint8(x_112, 16, x_123);
x_124 = lean_unbox(x_108);
lean_ctor_set_uint8(x_112, 17, x_124);
x_125 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_112);
x_126 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13;
x_127 = lean_box(0);
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_129, 0, x_112);
lean_ctor_set(x_129, 1, x_99);
lean_ctor_set(x_129, 2, x_105);
lean_ctor_set(x_129, 3, x_126);
lean_ctor_set(x_129, 4, x_127);
lean_ctor_set(x_129, 5, x_100);
lean_ctor_set(x_129, 6, x_128);
lean_ctor_set_uint64(x_129, sizeof(void*)*7, x_125);
lean_ctor_set_uint8(x_129, sizeof(void*)*7 + 8, x_94);
lean_ctor_set_uint8(x_129, sizeof(void*)*7 + 9, x_94);
lean_ctor_set_uint8(x_129, sizeof(void*)*7 + 10, x_94);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_103);
lean_inc(x_1);
x_130 = lean_infer_type(x_1, x_129, x_103, x_5, x_6, x_104);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_st_ref_get(x_103, x_132);
lean_dec(x_103);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_30 = x_100;
x_31 = x_94;
x_32 = x_5;
x_33 = x_101;
x_34 = x_99;
x_35 = x_131;
x_36 = x_134;
goto block_79;
}
else
{
lean_dec(x_103);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_130, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_130, 1);
lean_inc(x_136);
lean_dec(x_130);
x_30 = x_100;
x_31 = x_94;
x_32 = x_5;
x_33 = x_101;
x_34 = x_99;
x_35 = x_135;
x_36 = x_136;
goto block_79;
}
else
{
uint8_t x_137; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_130);
if (x_137 == 0)
{
return x_130;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_130, 0);
x_139 = lean_ctor_get(x_130, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_130);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_free_object(x_5);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_7);
return x_142;
}
}
else
{
lean_object* x_143; 
lean_free_object(x_5);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_143 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg(x_86, x_7);
return x_143;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; uint8_t x_159; 
x_144 = lean_ctor_get(x_5, 0);
x_145 = lean_ctor_get(x_5, 1);
x_146 = lean_ctor_get(x_5, 2);
x_147 = lean_ctor_get(x_5, 3);
x_148 = lean_ctor_get(x_5, 4);
x_149 = lean_ctor_get(x_5, 5);
x_150 = lean_ctor_get(x_5, 6);
x_151 = lean_ctor_get(x_5, 7);
x_152 = lean_ctor_get(x_5, 8);
x_153 = lean_ctor_get(x_5, 9);
x_154 = lean_ctor_get(x_5, 10);
x_155 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_156 = lean_ctor_get(x_5, 11);
x_157 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_158 = lean_ctor_get(x_5, 12);
lean_inc(x_158);
lean_inc(x_156);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_5);
x_159 = lean_nat_dec_eq(x_147, x_148);
if (x_159 == 0)
{
uint8_t x_160; 
x_160 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof(x_1);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; uint8_t x_182; uint8_t x_183; uint8_t x_184; uint8_t x_185; uint8_t x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; uint64_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_161 = lean_st_ref_get(x_2, x_7);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_box(0);
x_165 = lean_unsigned_to_nat(0u);
x_166 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_167 = lean_st_mk_ref(x_166, x_163);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_ctor_get(x_162, 0);
lean_inc(x_170);
lean_dec(x_162);
x_171 = lean_unsigned_to_nat(1u);
x_172 = lean_nat_add(x_147, x_171);
lean_dec(x_147);
x_173 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_173, 0, x_144);
lean_ctor_set(x_173, 1, x_145);
lean_ctor_set(x_173, 2, x_146);
lean_ctor_set(x_173, 3, x_172);
lean_ctor_set(x_173, 4, x_148);
lean_ctor_set(x_173, 5, x_149);
lean_ctor_set(x_173, 6, x_150);
lean_ctor_set(x_173, 7, x_151);
lean_ctor_set(x_173, 8, x_152);
lean_ctor_set(x_173, 9, x_153);
lean_ctor_set(x_173, 10, x_154);
lean_ctor_set(x_173, 11, x_156);
lean_ctor_set(x_173, 12, x_158);
lean_ctor_set_uint8(x_173, sizeof(void*)*13, x_155);
lean_ctor_set_uint8(x_173, sizeof(void*)*13 + 1, x_157);
x_174 = lean_box(1);
x_175 = lean_box(1);
x_176 = lean_box(0);
x_177 = lean_box(2);
x_178 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_178, 0, x_159);
lean_ctor_set_uint8(x_178, 1, x_159);
lean_ctor_set_uint8(x_178, 2, x_159);
lean_ctor_set_uint8(x_178, 3, x_159);
lean_ctor_set_uint8(x_178, 4, x_159);
x_179 = lean_unbox(x_174);
lean_ctor_set_uint8(x_178, 5, x_179);
x_180 = lean_unbox(x_174);
lean_ctor_set_uint8(x_178, 6, x_180);
lean_ctor_set_uint8(x_178, 7, x_159);
x_181 = lean_unbox(x_174);
lean_ctor_set_uint8(x_178, 8, x_181);
x_182 = lean_unbox(x_175);
lean_ctor_set_uint8(x_178, 9, x_182);
x_183 = lean_unbox(x_176);
lean_ctor_set_uint8(x_178, 10, x_183);
x_184 = lean_unbox(x_174);
lean_ctor_set_uint8(x_178, 11, x_184);
x_185 = lean_unbox(x_174);
lean_ctor_set_uint8(x_178, 12, x_185);
x_186 = lean_unbox(x_174);
lean_ctor_set_uint8(x_178, 13, x_186);
x_187 = lean_unbox(x_177);
lean_ctor_set_uint8(x_178, 14, x_187);
x_188 = lean_unbox(x_174);
lean_ctor_set_uint8(x_178, 15, x_188);
x_189 = lean_unbox(x_174);
lean_ctor_set_uint8(x_178, 16, x_189);
x_190 = lean_unbox(x_174);
lean_ctor_set_uint8(x_178, 17, x_190);
x_191 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_178);
x_192 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13;
x_193 = lean_box(0);
x_194 = lean_box(0);
x_195 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_195, 0, x_178);
lean_ctor_set(x_195, 1, x_164);
lean_ctor_set(x_195, 2, x_170);
lean_ctor_set(x_195, 3, x_192);
lean_ctor_set(x_195, 4, x_193);
lean_ctor_set(x_195, 5, x_165);
lean_ctor_set(x_195, 6, x_194);
lean_ctor_set_uint64(x_195, sizeof(void*)*7, x_191);
lean_ctor_set_uint8(x_195, sizeof(void*)*7 + 8, x_159);
lean_ctor_set_uint8(x_195, sizeof(void*)*7 + 9, x_159);
lean_ctor_set_uint8(x_195, sizeof(void*)*7 + 10, x_159);
lean_inc(x_6);
lean_inc(x_173);
lean_inc(x_168);
lean_inc(x_1);
x_196 = lean_infer_type(x_1, x_195, x_168, x_173, x_6, x_169);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_st_ref_get(x_168, x_198);
lean_dec(x_168);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
x_30 = x_165;
x_31 = x_159;
x_32 = x_173;
x_33 = x_166;
x_34 = x_164;
x_35 = x_197;
x_36 = x_200;
goto block_79;
}
else
{
lean_dec(x_168);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_196, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_196, 1);
lean_inc(x_202);
lean_dec(x_196);
x_30 = x_165;
x_31 = x_159;
x_32 = x_173;
x_33 = x_166;
x_34 = x_164;
x_35 = x_201;
x_36 = x_202;
goto block_79;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_173);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_203 = lean_ctor_get(x_196, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_196, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_205 = x_196;
} else {
 lean_dec_ref(x_196);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_204);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; 
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_207 = lean_box(0);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_7);
return x_208;
}
}
else
{
lean_object* x_209; 
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_209 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg(x_149, x_7);
return x_209;
}
}
block_29:
{
if (x_10 == 0)
{
lean_object* x_12; 
lean_inc(x_6);
lean_inc(x_9);
x_12 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_8, x_2, x_9, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(x_1, x_2, x_3, x_4, x_9, x_6, x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_12, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_11);
return x_28;
}
}
block_79:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint64_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_37 = lean_st_ref_get(x_2, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_st_mk_ref(x_33, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_box(1);
x_45 = lean_box(1);
x_46 = lean_box(0);
x_47 = lean_box(2);
x_48 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_48, 0, x_31);
lean_ctor_set_uint8(x_48, 1, x_31);
lean_ctor_set_uint8(x_48, 2, x_31);
lean_ctor_set_uint8(x_48, 3, x_31);
lean_ctor_set_uint8(x_48, 4, x_31);
x_49 = lean_unbox(x_44);
lean_ctor_set_uint8(x_48, 5, x_49);
x_50 = lean_unbox(x_44);
lean_ctor_set_uint8(x_48, 6, x_50);
lean_ctor_set_uint8(x_48, 7, x_31);
x_51 = lean_unbox(x_44);
lean_ctor_set_uint8(x_48, 8, x_51);
x_52 = lean_unbox(x_45);
lean_ctor_set_uint8(x_48, 9, x_52);
x_53 = lean_unbox(x_46);
lean_ctor_set_uint8(x_48, 10, x_53);
x_54 = lean_unbox(x_44);
lean_ctor_set_uint8(x_48, 11, x_54);
x_55 = lean_unbox(x_44);
lean_ctor_set_uint8(x_48, 12, x_55);
x_56 = lean_unbox(x_44);
lean_ctor_set_uint8(x_48, 13, x_56);
x_57 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, 14, x_57);
x_58 = lean_unbox(x_44);
lean_ctor_set_uint8(x_48, 15, x_58);
x_59 = lean_unbox(x_44);
lean_ctor_set_uint8(x_48, 16, x_59);
x_60 = lean_unbox(x_44);
lean_ctor_set_uint8(x_48, 17, x_60);
x_61 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_48);
x_62 = lean_mk_empty_array_with_capacity(x_30);
x_63 = lean_box(0);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_65, 0, x_48);
lean_ctor_set(x_65, 1, x_34);
lean_ctor_set(x_65, 2, x_43);
lean_ctor_set(x_65, 3, x_62);
lean_ctor_set(x_65, 4, x_63);
lean_ctor_set(x_65, 5, x_30);
lean_ctor_set(x_65, 6, x_64);
lean_ctor_set_uint64(x_65, sizeof(void*)*7, x_61);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 8, x_31);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 9, x_31);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 10, x_31);
lean_inc(x_6);
lean_inc(x_32);
lean_inc(x_41);
lean_inc(x_35);
x_66 = l_Lean_Meta_isProp(x_35, x_65, x_41, x_32, x_6, x_42);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_st_ref_get(x_41, x_68);
lean_dec(x_41);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_unbox(x_67);
lean_dec(x_67);
x_8 = x_35;
x_9 = x_32;
x_10 = x_71;
x_11 = x_70;
goto block_29;
}
else
{
lean_dec(x_41);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_66, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_dec(x_66);
x_74 = lean_unbox(x_72);
lean_dec(x_72);
x_8 = x_35;
x_9 = x_32;
x_10 = x_74;
x_11 = x_73;
goto block_29;
}
else
{
uint8_t x_75; 
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_66);
if (x_75 == 0)
{
return x_66;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_66, 0);
x_77 = lean_ctor_get(x_66, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_66);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_f", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_12, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toCode(x_14, x_2, x_3, x_4, x_5, x_6, x_15);
lean_dec(x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__1;
x_20 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_11, x_17, x_19, x_3, x_4, x_5, x_6, x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_8);
if (x_29 == 0)
{
return x_8;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_8, 0);
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_8);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_31; uint8_t x_32; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0), 7, 1);
lean_closure_set(x_12, 0, x_1);
x_31 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit(x_1);
x_32 = l_Lean_Expr_isLambda(x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand(x_11, x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_12);
x_34 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_31, x_2, x_3, x_4, x_5, x_6, x_10);
return x_34;
}
else
{
lean_dec(x_31);
goto block_30;
}
}
else
{
lean_dec(x_31);
lean_dec(x_11);
goto block_30;
}
block_30:
{
lean_object* x_13; 
lean_inc(x_2);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg(x_12, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_16, x_2, x_15);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_13);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
x_16 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_4);
return x_16;
}
default: 
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_3, x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_12, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_17, x_2, x_14);
x_2 = x_19;
x_3 = x_20;
x_9 = x_15;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_get_projection_info(x_7, x_1);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_get_projection_info(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1___redArg(x_1, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_array_set(x_2, x_3, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
lean_dec(x_3);
x_1 = x_10;
x_2 = x_12;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_array_set(x_2, x_3, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
lean_dec(x_3);
x_1 = x_10;
x_2 = x_12;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
switch (lean_obj_tag(x_17)) {
case 0:
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_16;
}
case 1:
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_size(x_2);
x_21 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0(x_20, x_21, x_2, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
x_27 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_25, x_26, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_4);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
default: 
{
uint8_t x_32; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_16, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_16, 0, x_34);
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_dec(x_16);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_array_set(x_2, x_3, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
x_15 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3_spec__3(x_10, x_12, x_14, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
else
{
lean_object* x_16; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
switch (lean_obj_tag(x_17)) {
case 0:
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_16;
}
case 1:
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_size(x_2);
x_21 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0(x_20, x_21, x_2, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
x_27 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_25, x_26, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_4);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
default: 
{
uint8_t x_32; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_16, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_16, 0, x_34);
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_dec(x_16);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_16;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Quot", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lift", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mk", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("casesOn", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rec", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("recOn", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEq", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("And", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Iff", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__21;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Empty", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__23;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__21;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__23;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Expr_letFunAppArgs_x3f(x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_Expr_getAppFn(x_1);
x_20 = lean_csimp_replace_constants(x_18, x_19);
if (lean_obj_tag(x_20) == 4)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2;
x_23 = lean_name_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4;
x_25 = lean_name_eq(x_21, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6;
x_27 = lean_name_eq(x_21, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8;
x_29 = lean_name_eq(x_21, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10;
x_31 = lean_name_eq(x_21, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2;
x_33 = lean_name_eq(x_21, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12;
x_35 = lean_name_eq(x_21, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13;
x_37 = lean_name_eq(x_21, x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__14;
x_39 = lean_name_eq(x_21, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__16;
x_41 = lean_name_eq(x_21, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__18;
x_43 = lean_name_eq(x_21, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__19;
x_45 = lean_name_eq(x_21, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__20;
x_47 = lean_name_eq(x_21, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22;
x_49 = lean_name_eq(x_21, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__24;
x_51 = lean_name_eq(x_21, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__25;
x_53 = lean_name_eq(x_21, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__26;
x_55 = lean_name_eq(x_21, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_21);
x_56 = l_Lean_Compiler_LCNF_getCasesInfo_x3f(x_21, x_5, x_6, x_11);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_21);
x_59 = l_Lean_Compiler_LCNF_getCtorArity_x3f(x_21, x_5, x_6, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_st_ref_get(x_6, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_21);
x_66 = lean_is_no_confusion(x_65, x_21);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1___redArg(x_21, x_6, x_64);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__27;
x_71 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_71);
x_72 = lean_mk_array(x_71, x_70);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_sub(x_71, x_73);
lean_dec(x_71);
x_75 = l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__2(x_1, x_72, x_74, x_2, x_3, x_4, x_5, x_6, x_69);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_67, 1);
lean_inc(x_76);
lean_dec(x_67);
x_77 = lean_ctor_get(x_68, 0);
lean_inc(x_77);
lean_dec(x_68);
x_78 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(x_77, x_1, x_2, x_3, x_4, x_5, x_6, x_76);
lean_dec(x_77);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_21);
x_79 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion(x_1, x_2, x_3, x_4, x_5, x_6, x_64);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_21);
x_80 = lean_ctor_get(x_59, 1);
lean_inc(x_80);
lean_dec(x_59);
x_81 = lean_ctor_get(x_60, 0);
lean_inc(x_81);
lean_dec(x_60);
x_82 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(x_81, x_1, x_2, x_3, x_4, x_5, x_6, x_80);
lean_dec(x_81);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_59);
if (x_83 == 0)
{
return x_59;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_59, 0);
x_85 = lean_ctor_get(x_59, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_59);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_21);
x_87 = lean_ctor_get(x_56, 1);
lean_inc(x_87);
lean_dec(x_56);
x_88 = lean_ctor_get(x_57, 0);
lean_inc(x_88);
lean_dec(x_57);
x_89 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(x_88, x_1, x_2, x_3, x_4, x_5, x_6, x_87);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_56);
if (x_90 == 0)
{
return x_56;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_56, 0);
x_92 = lean_ctor_get(x_56, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_56);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; 
lean_dec(x_21);
x_94 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_94;
}
}
else
{
lean_object* x_95; 
lean_dec(x_21);
x_95 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_95;
}
}
else
{
lean_object* x_96; 
lean_dec(x_21);
x_96 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_96;
}
}
else
{
lean_object* x_97; 
lean_dec(x_21);
x_97 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_97;
}
}
else
{
lean_dec(x_21);
goto block_14;
}
}
else
{
lean_dec(x_21);
goto block_14;
}
}
else
{
lean_dec(x_21);
goto block_17;
}
}
else
{
lean_dec(x_21);
goto block_17;
}
}
else
{
lean_object* x_98; 
lean_dec(x_21);
x_98 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_98;
}
}
else
{
lean_object* x_99; 
lean_dec(x_21);
x_99 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_99;
}
}
else
{
lean_object* x_100; 
lean_dec(x_21);
x_100 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_100;
}
}
else
{
lean_object* x_101; 
lean_dec(x_21);
x_101 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_101;
}
}
else
{
lean_object* x_102; 
lean_dec(x_21);
x_102 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_102;
}
}
else
{
lean_object* x_103; 
lean_dec(x_21);
x_103 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_103;
}
}
else
{
lean_object* x_104; 
lean_dec(x_21);
x_104 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_21);
x_105 = lean_unsigned_to_nat(3u);
x_106 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(x_105, x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_106;
}
}
else
{
lean_object* x_107; 
lean_dec(x_21);
x_107 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_20);
x_108 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__27;
x_109 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_109);
x_110 = lean_mk_array(x_109, x_108);
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_nat_sub(x_109, x_111);
lean_dec(x_109);
x_113 = l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3(x_1, x_110, x_112, x_2, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_112);
return x_113;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(4u);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(x_1, x_12, x_2, x_3, x_4, x_5, x_6, x_11);
return x_13;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_11);
return x_16;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_1);
x_114 = lean_ctor_get(x_8, 0);
lean_inc(x_114);
lean_dec(x_8);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 0);
lean_inc(x_118);
lean_dec(x_114);
x_119 = lean_ctor_get(x_115, 0);
lean_inc(x_119);
lean_dec(x_115);
x_120 = lean_ctor_get(x_116, 0);
lean_inc(x_120);
lean_dec(x_116);
x_121 = lean_ctor_get(x_117, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_117, 1);
lean_inc(x_122);
lean_dec(x_117);
x_123 = lean_box(1);
x_124 = lean_unbox(x_123);
x_125 = l_Lean_Expr_letE___override(x_119, x_120, x_121, x_122, x_124);
x_126 = l_Lean_mkAppN(x_125, x_118);
lean_dec(x_118);
x_127 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(x_126, x_2, x_3, x_4, x_5, x_6, x_7);
return x_127;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_61 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof(x_1);
if (x_61 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; uint64_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_110 = lean_st_ref_get(x_2, x_7);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_box(0);
x_114 = lean_unsigned_to_nat(0u);
x_115 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_116 = lean_st_mk_ref(x_115, x_112);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_ctor_get(x_111, 0);
lean_inc(x_119);
lean_dec(x_111);
x_120 = lean_box(1);
x_121 = lean_box(1);
x_122 = lean_box(0);
x_123 = lean_box(2);
x_124 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_124, 0, x_61);
lean_ctor_set_uint8(x_124, 1, x_61);
lean_ctor_set_uint8(x_124, 2, x_61);
lean_ctor_set_uint8(x_124, 3, x_61);
lean_ctor_set_uint8(x_124, 4, x_61);
x_125 = lean_unbox(x_120);
lean_ctor_set_uint8(x_124, 5, x_125);
x_126 = lean_unbox(x_120);
lean_ctor_set_uint8(x_124, 6, x_126);
lean_ctor_set_uint8(x_124, 7, x_61);
x_127 = lean_unbox(x_120);
lean_ctor_set_uint8(x_124, 8, x_127);
x_128 = lean_unbox(x_121);
lean_ctor_set_uint8(x_124, 9, x_128);
x_129 = lean_unbox(x_122);
lean_ctor_set_uint8(x_124, 10, x_129);
x_130 = lean_unbox(x_120);
lean_ctor_set_uint8(x_124, 11, x_130);
x_131 = lean_unbox(x_120);
lean_ctor_set_uint8(x_124, 12, x_131);
x_132 = lean_unbox(x_120);
lean_ctor_set_uint8(x_124, 13, x_132);
x_133 = lean_unbox(x_123);
lean_ctor_set_uint8(x_124, 14, x_133);
x_134 = lean_unbox(x_120);
lean_ctor_set_uint8(x_124, 15, x_134);
x_135 = lean_unbox(x_120);
lean_ctor_set_uint8(x_124, 16, x_135);
x_136 = lean_unbox(x_120);
lean_ctor_set_uint8(x_124, 17, x_136);
x_137 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_124);
x_138 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13;
x_139 = lean_box(0);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_141, 0, x_124);
lean_ctor_set(x_141, 1, x_113);
lean_ctor_set(x_141, 2, x_119);
lean_ctor_set(x_141, 3, x_138);
lean_ctor_set(x_141, 4, x_139);
lean_ctor_set(x_141, 5, x_114);
lean_ctor_set(x_141, 6, x_140);
lean_ctor_set_uint64(x_141, sizeof(void*)*7, x_137);
lean_ctor_set_uint8(x_141, sizeof(void*)*7 + 8, x_61);
lean_ctor_set_uint8(x_141, sizeof(void*)*7 + 9, x_61);
lean_ctor_set_uint8(x_141, sizeof(void*)*7 + 10, x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_117);
lean_inc(x_1);
x_142 = lean_infer_type(x_1, x_141, x_117, x_5, x_6, x_118);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_st_ref_get(x_117, x_144);
lean_dec(x_117);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_62 = x_143;
x_63 = x_146;
goto block_109;
}
else
{
lean_dec(x_117);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_142, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_142, 1);
lean_inc(x_148);
lean_dec(x_142);
x_62 = x_147;
x_63 = x_148;
goto block_109;
}
else
{
uint8_t x_149; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_142);
if (x_149 == 0)
{
return x_142;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_142, 0);
x_151 = lean_ctor_get(x_142, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_142);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = lean_box(0);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_7);
return x_154;
}
block_60:
{
if (x_9 == 0)
{
lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_8);
x_11 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_8, x_2, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(x_1, x_2, x_3, x_4, x_5, x_6, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_8, x_2, x_5, x_6, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l_Lean_Compiler_LCNF_isPredicateType(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_free_object(x_17);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_1, x_2, x_5, x_6, x_20);
lean_dec(x_2);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
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
lean_object* x_34; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_box(0);
lean_ctor_set(x_17, 0, x_34);
return x_17;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_17, 0);
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_17);
x_37 = l_Lean_Compiler_LCNF_isPredicateType(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_1, x_2, x_5, x_6, x_36);
lean_dec(x_2);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
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
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_39);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_46 = x_38;
} else {
 lean_dec_ref(x_38);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_36);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_17);
if (x_50 == 0)
{
return x_17;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_17, 0);
x_52 = lean_ctor_get(x_17, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_17);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_11);
if (x_54 == 0)
{
return x_11;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_11, 0);
x_56 = lean_ctor_get(x_11, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_11);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_10);
return x_59;
}
}
block_109:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint64_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_64 = lean_st_ref_get(x_2, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_box(0);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_70 = lean_st_mk_ref(x_69, x_66);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_65, 0);
lean_inc(x_73);
lean_dec(x_65);
x_74 = lean_box(1);
x_75 = lean_box(1);
x_76 = lean_box(0);
x_77 = lean_box(2);
x_78 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_78, 0, x_61);
lean_ctor_set_uint8(x_78, 1, x_61);
lean_ctor_set_uint8(x_78, 2, x_61);
lean_ctor_set_uint8(x_78, 3, x_61);
lean_ctor_set_uint8(x_78, 4, x_61);
x_79 = lean_unbox(x_74);
lean_ctor_set_uint8(x_78, 5, x_79);
x_80 = lean_unbox(x_74);
lean_ctor_set_uint8(x_78, 6, x_80);
lean_ctor_set_uint8(x_78, 7, x_61);
x_81 = lean_unbox(x_74);
lean_ctor_set_uint8(x_78, 8, x_81);
x_82 = lean_unbox(x_75);
lean_ctor_set_uint8(x_78, 9, x_82);
x_83 = lean_unbox(x_76);
lean_ctor_set_uint8(x_78, 10, x_83);
x_84 = lean_unbox(x_74);
lean_ctor_set_uint8(x_78, 11, x_84);
x_85 = lean_unbox(x_74);
lean_ctor_set_uint8(x_78, 12, x_85);
x_86 = lean_unbox(x_74);
lean_ctor_set_uint8(x_78, 13, x_86);
x_87 = lean_unbox(x_77);
lean_ctor_set_uint8(x_78, 14, x_87);
x_88 = lean_unbox(x_74);
lean_ctor_set_uint8(x_78, 15, x_88);
x_89 = lean_unbox(x_74);
lean_ctor_set_uint8(x_78, 16, x_89);
x_90 = lean_unbox(x_74);
lean_ctor_set_uint8(x_78, 17, x_90);
x_91 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_78);
x_92 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13;
x_93 = lean_box(0);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_95, 0, x_78);
lean_ctor_set(x_95, 1, x_67);
lean_ctor_set(x_95, 2, x_73);
lean_ctor_set(x_95, 3, x_92);
lean_ctor_set(x_95, 4, x_93);
lean_ctor_set(x_95, 5, x_68);
lean_ctor_set(x_95, 6, x_94);
lean_ctor_set_uint64(x_95, sizeof(void*)*7, x_91);
lean_ctor_set_uint8(x_95, sizeof(void*)*7 + 8, x_61);
lean_ctor_set_uint8(x_95, sizeof(void*)*7 + 9, x_61);
lean_ctor_set_uint8(x_95, sizeof(void*)*7 + 10, x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_71);
lean_inc(x_62);
x_96 = l_Lean_Meta_isProp(x_62, x_95, x_71, x_5, x_6, x_72);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_st_ref_get(x_71, x_98);
lean_dec(x_71);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_unbox(x_97);
lean_dec(x_97);
x_8 = x_62;
x_9 = x_101;
x_10 = x_100;
goto block_60;
}
else
{
lean_dec(x_71);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_ctor_get(x_96, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_96, 1);
lean_inc(x_103);
lean_dec(x_96);
x_104 = lean_unbox(x_102);
lean_dec(x_102);
x_8 = x_62;
x_9 = x_104;
x_10 = x_103;
goto block_60;
}
else
{
uint8_t x_105; 
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_96);
if (x_105 == 0)
{
return x_96;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_96, 0);
x_107 = lean_ctor_get(x_96, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_96);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitAppDefaultConst", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__2;
x_2 = lean_unsigned_to_nat(68u);
x_3 = lean_unsigned_to_nat(477u);
x_4 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__0;
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_13 = lean_csimp_replace_constants(x_12, x_1);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_size(x_2);
x_17 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0(x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_19);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
x_23 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_21, x_22, x_3, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_3);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_13);
lean_dec(x_2);
x_28 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1;
x_29 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_28, x_3, x_4, x_5, x_6, x_7, x_11);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 5);
x_8 = lean_st_ref_get(x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_st_ref_get(x_2, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_dec(x_18);
x_19 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec(x_17);
x_20 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__7;
lean_inc(x_6);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_19);
lean_ctor_set(x_21, 3, x_6);
lean_ctor_set_tag(x_14, 3);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 0, x_21);
lean_inc(x_7);
lean_ctor_set(x_8, 1, x_14);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_8);
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_22);
lean_dec(x_22);
x_24 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__7;
lean_inc(x_6);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_6);
x_26 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_1);
lean_inc(x_7);
lean_ctor_set(x_8, 1, x_26);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_8);
return x_12;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_31 = x_27;
} else {
 lean_dec_ref(x_27);
 x_31 = lean_box(0);
}
x_32 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_30);
lean_dec(x_30);
x_33 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__7;
lean_inc(x_6);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_6);
if (lean_is_scalar(x_31)) {
 x_35 = lean_alloc_ctor(3, 2, 0);
} else {
 x_35 = x_31;
 lean_ctor_set_tag(x_35, 3);
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_1);
lean_inc(x_7);
lean_ctor_set(x_8, 1, x_35);
lean_ctor_set(x_8, 0, x_7);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_8);
lean_ctor_set(x_36, 1, x_28);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_37 = lean_ctor_get(x_8, 0);
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_8);
x_39 = lean_st_ref_get(x_2, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_45 = x_40;
} else {
 lean_dec_ref(x_40);
 x_45 = lean_box(0);
}
x_46 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_44);
lean_dec(x_44);
x_47 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__7;
lean_inc(x_6);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_46);
lean_ctor_set(x_48, 3, x_6);
if (lean_is_scalar(x_45)) {
 x_49 = lean_alloc_ctor(3, 2, 0);
} else {
 x_49 = x_45;
 lean_ctor_set_tag(x_49, 3);
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_1);
lean_inc(x_7);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_7);
lean_ctor_set(x_50, 1, x_49);
if (lean_is_scalar(x_42)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_42;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_41);
return x_51;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown constant '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
lean_inc(x_1);
x_15 = l_Lean_Environment_find_x3f(x_12, x_1, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_8);
x_16 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__1;
x_17 = lean_unbox(x_13);
x_18 = l_Lean_MessageData_ofConstName(x_1, x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__3;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(x_21, x_4, x_5, x_6, x_11);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
lean_ctor_set(x_8, 0, x_23);
return x_8;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = lean_unbox(x_27);
lean_inc(x_1);
x_29 = l_Lean_Environment_find_x3f(x_26, x_1, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__1;
x_31 = lean_unbox(x_27);
x_32 = l_Lean_MessageData_ofConstName(x_1, x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__3;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(x_35, x_4, x_5, x_6, x_25);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_25);
return x_38;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitProjFn", 44, 44);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__2;
x_2 = lean_unsigned_to_nat(45u);
x_3 = lean_unsigned_to_nat(667u);
x_4 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__0;
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_9) == 0)
{
x_11 = x_9;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_9, 0);
x_11 = x_60;
goto block_59;
}
block_59:
{
uint8_t x_12; 
x_12 = l_Lean_Compiler_LCNF_isRuntimeBultinType(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0(x_14, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Core_instantiateValueLevelParams(x_17, x_15, x_6, x_7, x_18);
lean_dec(x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__27;
x_23 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_23);
x_24 = lean_mk_array(x_23, x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_23, x_25);
lean_dec(x_23);
x_27 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_24, x_26);
x_28 = l_Lean_Expr_beta(x_20, x_27);
x_29 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_28, x_3, x_4, x_5, x_6, x_7, x_21);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
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
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_16, 0);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_16);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_13);
lean_dec(x_2);
x_38 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1;
x_39 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_38, x_3, x_4, x_5, x_6, x_7, x_8);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = l_Lean_Expr_getAppNumArgs(x_2);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_10, x_41);
x_43 = lean_nat_dec_lt(x_40, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_42);
x_44 = l_Lean_Expr_getAppFn(x_2);
x_45 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__27;
lean_inc(x_40);
x_46 = lean_mk_array(x_40, x_45);
x_47 = lean_nat_sub(x_40, x_41);
lean_dec(x_40);
x_48 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_46, x_47);
x_49 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(x_44, x_48, x_3, x_4, x_5, x_6, x_7, x_8);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_nat_sub(x_42, x_40);
lean_dec(x_40);
lean_dec(x_42);
lean_inc(x_7);
lean_inc(x_6);
x_51 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_2, x_50, x_3, x_6, x_7, x_8);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_52, x_3, x_4, x_5, x_6, x_7, x_53);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_51);
if (x_55 == 0)
{
return x_51;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_51, 0);
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_51);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg(x_1, x_2, x_5, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_get_size(x_3);
x_15 = l_Array_toSubarray___redArg(x_3, x_4, x_14);
x_16 = l_Array_ofSubarray___redArg(x_15);
lean_dec(x_15);
x_17 = l_Lean_mkAppN(x_12, x_16);
lean_dec(x_16);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_17, x_5, x_6, x_7, x_8, x_9, x_13);
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
lean_dec(x_4);
lean_dec(x_3);
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
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("code generator failed, unsupported occurrence of `", 50, 50);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_29; lean_object* x_30; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_134; lean_object* x_135; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint64_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; uint8_t x_190; uint8_t x_191; lean_object* x_192; 
x_170 = lean_st_ref_get(x_10, x_15);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_box(0);
x_174 = lean_unsigned_to_nat(0u);
x_175 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_176 = lean_st_mk_ref(x_175, x_172);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_ctor_get(x_171, 0);
lean_inc(x_179);
lean_dec(x_171);
x_180 = lean_nat_add(x_7, x_8);
lean_inc(x_5);
x_181 = lean_array_get(x_5, x_6, x_180);
lean_dec(x_180);
x_182 = lean_box(0);
x_183 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_184 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_185 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13;
x_186 = lean_box(0);
x_187 = lean_box(0);
x_188 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_173);
lean_ctor_set(x_188, 2, x_179);
lean_ctor_set(x_188, 3, x_185);
lean_ctor_set(x_188, 4, x_186);
lean_ctor_set(x_188, 5, x_174);
lean_ctor_set(x_188, 6, x_187);
lean_ctor_set_uint64(x_188, sizeof(void*)*7, x_184);
x_189 = lean_unbox(x_182);
lean_ctor_set_uint8(x_188, sizeof(void*)*7 + 8, x_189);
x_190 = lean_unbox(x_182);
lean_ctor_set_uint8(x_188, sizeof(void*)*7 + 9, x_190);
x_191 = lean_unbox(x_182);
lean_ctor_set_uint8(x_188, sizeof(void*)*7 + 10, x_191);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_177);
x_192 = lean_whnf(x_181, x_188, x_177, x_13, x_14, x_178);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_st_ref_get(x_177, x_194);
lean_dec(x_177);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
lean_dec(x_195);
x_134 = x_193;
x_135 = x_196;
goto block_169;
}
else
{
lean_dec(x_177);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_192, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_192, 1);
lean_inc(x_198);
lean_dec(x_192);
x_134 = x_197;
x_135 = x_198;
goto block_169;
}
else
{
uint8_t x_199; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_192);
if (x_199 == 0)
{
return x_192;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_192, 0);
x_201 = lean_ctor_get(x_192, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_192);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
block_28:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
lean_dec(x_16);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__1;
x_23 = l_Lean_MessageData_ofName(x_1);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__3;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(x_26, x_18, x_19, x_20, x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
return x_27;
}
block_39:
{
lean_object* x_31; 
lean_inc(x_14);
lean_inc(x_13);
x_31 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_29, x_10, x_13, x_14, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_32, x_10, x_11, x_12, x_13, x_14, x_33);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
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
block_98:
{
if (lean_obj_tag(x_42) == 0)
{
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_16 = x_10;
x_17 = x_11;
x_18 = x_12;
x_19 = x_13;
x_20 = x_14;
x_21 = x_45;
goto block_28;
}
else
{
if (lean_obj_tag(x_44) == 0)
{
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_16 = x_10;
x_17 = x_11;
x_18 = x_12;
x_19 = x_13;
x_20 = x_14;
x_21 = x_45;
goto block_28;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_1);
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_46, 4);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_ctor_get(x_47, 0);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_name_eq(x_51, x_52);
lean_dec(x_52);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint64_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_50);
lean_dec(x_6);
lean_dec(x_5);
x_54 = lean_st_ref_get(x_10, x_45);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_st_mk_ref(x_40, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_box(1);
x_62 = lean_box(1);
x_63 = lean_box(0);
x_64 = lean_box(2);
x_65 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_65, 0, x_53);
lean_ctor_set_uint8(x_65, 1, x_53);
lean_ctor_set_uint8(x_65, 2, x_53);
lean_ctor_set_uint8(x_65, 3, x_53);
lean_ctor_set_uint8(x_65, 4, x_53);
x_66 = lean_unbox(x_61);
lean_ctor_set_uint8(x_65, 5, x_66);
x_67 = lean_unbox(x_61);
lean_ctor_set_uint8(x_65, 6, x_67);
lean_ctor_set_uint8(x_65, 7, x_53);
x_68 = lean_unbox(x_61);
lean_ctor_set_uint8(x_65, 8, x_68);
x_69 = lean_unbox(x_62);
lean_ctor_set_uint8(x_65, 9, x_69);
x_70 = lean_unbox(x_63);
lean_ctor_set_uint8(x_65, 10, x_70);
x_71 = lean_unbox(x_61);
lean_ctor_set_uint8(x_65, 11, x_71);
x_72 = lean_unbox(x_61);
lean_ctor_set_uint8(x_65, 12, x_72);
x_73 = lean_unbox(x_61);
lean_ctor_set_uint8(x_65, 13, x_73);
x_74 = lean_unbox(x_64);
lean_ctor_set_uint8(x_65, 14, x_74);
x_75 = lean_unbox(x_61);
lean_ctor_set_uint8(x_65, 15, x_75);
x_76 = lean_unbox(x_61);
lean_ctor_set_uint8(x_65, 16, x_76);
x_77 = lean_unbox(x_61);
lean_ctor_set_uint8(x_65, 17, x_77);
x_78 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_65);
x_79 = lean_mk_empty_array_with_capacity(x_41);
x_80 = lean_box(0);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_82, 0, x_65);
lean_ctor_set(x_82, 1, x_43);
lean_ctor_set(x_82, 2, x_60);
lean_ctor_set(x_82, 3, x_79);
lean_ctor_set(x_82, 4, x_80);
lean_ctor_set(x_82, 5, x_41);
lean_ctor_set(x_82, 6, x_81);
lean_ctor_set_uint64(x_82, sizeof(void*)*7, x_78);
lean_ctor_set_uint8(x_82, sizeof(void*)*7 + 8, x_53);
lean_ctor_set_uint8(x_82, sizeof(void*)*7 + 9, x_53);
lean_ctor_set_uint8(x_82, sizeof(void*)*7 + 10, x_53);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_58);
x_83 = lean_infer_type(x_2, x_82, x_58, x_13, x_14, x_59);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_st_ref_get(x_58, x_85);
lean_dec(x_58);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_29 = x_84;
x_30 = x_87;
goto block_39;
}
else
{
lean_dec(x_58);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_dec(x_83);
x_29 = x_88;
x_30 = x_89;
goto block_39;
}
else
{
uint8_t x_90; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_90 = !lean_is_exclusive(x_83);
if (x_90 == 0)
{
return x_83;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_83, 0);
x_92 = lean_ctor_get(x_83, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_83);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_40);
x_94 = lean_nat_add(x_3, x_4);
x_95 = lean_array_get(x_5, x_6, x_3);
lean_inc(x_94);
x_96 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__0), 10, 4);
lean_closure_set(x_96, 0, x_95);
lean_closure_set(x_96, 1, x_50);
lean_closure_set(x_96, 2, x_6);
lean_closure_set(x_96, 3, x_94);
x_97 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_2, x_94, x_96, x_10, x_11, x_12, x_13, x_14, x_45);
lean_dec(x_94);
return x_97;
}
}
}
}
block_133:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint64_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; lean_object* x_122; 
x_105 = lean_st_ref_get(x_10, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
lean_inc(x_99);
x_108 = lean_st_mk_ref(x_99, x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_106, 0);
lean_inc(x_111);
lean_dec(x_106);
x_112 = lean_box(0);
x_113 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_114 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_115 = lean_mk_empty_array_with_capacity(x_100);
x_116 = lean_box(0);
x_117 = lean_box(0);
lean_inc(x_100);
lean_inc(x_101);
x_118 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_118, 0, x_113);
lean_ctor_set(x_118, 1, x_101);
lean_ctor_set(x_118, 2, x_111);
lean_ctor_set(x_118, 3, x_115);
lean_ctor_set(x_118, 4, x_116);
lean_ctor_set(x_118, 5, x_100);
lean_ctor_set(x_118, 6, x_117);
lean_ctor_set_uint64(x_118, sizeof(void*)*7, x_114);
x_119 = lean_unbox(x_112);
lean_ctor_set_uint8(x_118, sizeof(void*)*7 + 8, x_119);
x_120 = lean_unbox(x_112);
lean_ctor_set_uint8(x_118, sizeof(void*)*7 + 9, x_120);
x_121 = lean_unbox(x_112);
lean_ctor_set_uint8(x_118, sizeof(void*)*7 + 10, x_121);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_109);
x_122 = l_Lean_Meta_isConstructorApp_x3f(x_102, x_118, x_109, x_13, x_14, x_110);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_st_ref_get(x_109, x_124);
lean_dec(x_109);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_40 = x_99;
x_41 = x_100;
x_42 = x_103;
x_43 = x_101;
x_44 = x_123;
x_45 = x_126;
goto block_98;
}
else
{
lean_dec(x_109);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_122, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_122, 1);
lean_inc(x_128);
lean_dec(x_122);
x_40 = x_99;
x_41 = x_100;
x_42 = x_103;
x_43 = x_101;
x_44 = x_127;
x_45 = x_128;
goto block_98;
}
else
{
uint8_t x_129; 
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_122);
if (x_129 == 0)
{
return x_122;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_122, 0);
x_131 = lean_ctor_get(x_122, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_122);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
block_169:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint64_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; lean_object* x_158; 
x_136 = lean_st_ref_get(x_10, x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_box(0);
x_140 = lean_unsigned_to_nat(0u);
x_141 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_142 = lean_st_mk_ref(x_141, x_138);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_ctor_get(x_137, 0);
lean_inc(x_145);
lean_dec(x_137);
x_146 = l_Lean_Expr_toCtorIfLit(x_9);
x_147 = l_Lean_Expr_toCtorIfLit(x_134);
x_148 = lean_box(0);
x_149 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_150 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_151 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13;
x_152 = lean_box(0);
x_153 = lean_box(0);
x_154 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_154, 0, x_149);
lean_ctor_set(x_154, 1, x_139);
lean_ctor_set(x_154, 2, x_145);
lean_ctor_set(x_154, 3, x_151);
lean_ctor_set(x_154, 4, x_152);
lean_ctor_set(x_154, 5, x_140);
lean_ctor_set(x_154, 6, x_153);
lean_ctor_set_uint64(x_154, sizeof(void*)*7, x_150);
x_155 = lean_unbox(x_148);
lean_ctor_set_uint8(x_154, sizeof(void*)*7 + 8, x_155);
x_156 = lean_unbox(x_148);
lean_ctor_set_uint8(x_154, sizeof(void*)*7 + 9, x_156);
x_157 = lean_unbox(x_148);
lean_ctor_set_uint8(x_154, sizeof(void*)*7 + 10, x_157);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_143);
x_158 = l_Lean_Meta_isConstructorApp_x3f(x_146, x_154, x_143, x_13, x_14, x_144);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_st_ref_get(x_143, x_160);
lean_dec(x_143);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_99 = x_141;
x_100 = x_140;
x_101 = x_139;
x_102 = x_147;
x_103 = x_159;
x_104 = x_162;
goto block_133;
}
else
{
lean_dec(x_143);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_158, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_158, 1);
lean_inc(x_164);
lean_dec(x_158);
x_99 = x_141;
x_100 = x_140;
x_101 = x_139;
x_102 = x_147;
x_103 = x_163;
x_104 = x_164;
goto block_133;
}
else
{
uint8_t x_165; 
lean_dec(x_147);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_165 = !lean_is_exclusive(x_158);
if (x_165 == 0)
{
return x_158;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_158, 0);
x_167 = lean_ctor_get(x_158, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_158);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_15 = lean_st_mk_ref(x_14, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_box(0);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_21 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_22 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13;
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set(x_25, 5, x_13);
lean_ctor_set(x_25, 6, x_24);
lean_ctor_set_uint64(x_25, sizeof(void*)*7, x_21);
x_26 = lean_unbox(x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 8, x_26);
x_27 = lean_unbox(x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 9, x_27);
x_28 = lean_unbox(x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 10, x_28);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_16);
x_29 = lean_whnf(x_1, x_25, x_16, x_6, x_7, x_17);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_st_ref_get(x_16, x_31);
lean_dec(x_16);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_apply_7(x_2, x_30, x_3, x_4, x_5, x_6, x_7, x_33);
return x_34;
}
else
{
lean_dec(x_16);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_apply_7(x_2, x_35, x_3, x_4, x_5, x_6, x_7, x_36);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
return x_29;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_29);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitNoConfusion", 49, 49);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__2;
x_2 = lean_unsigned_to_nat(56u);
x_3 = lean_unsigned_to_nat(625u);
x_4 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__0;
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__2;
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_unsigned_to_nat(623u);
x_4 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__0;
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_instInhabitedExpr;
if (lean_obj_tag(x_9) == 0)
{
x_11 = x_9;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_9, 0);
lean_inc(x_41);
x_11 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_12; 
x_12 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 5)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_nat_add(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_18, x_19);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_add(x_20, x_21);
x_23 = lean_nat_add(x_22, x_19);
lean_dec(x_22);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__27;
x_25 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_25);
x_26 = lean_mk_array(x_25, x_24);
x_27 = lean_nat_sub(x_25, x_19);
lean_dec(x_25);
lean_inc(x_1);
x_28 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_26, x_27);
lean_inc(x_28);
lean_inc(x_23);
lean_inc(x_1);
x_29 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___boxed), 15, 8);
lean_closure_set(x_29, 0, x_9);
lean_closure_set(x_29, 1, x_1);
lean_closure_set(x_29, 2, x_23);
lean_closure_set(x_29, 3, x_19);
lean_closure_set(x_29, 4, x_10);
lean_closure_set(x_29, 5, x_28);
lean_closure_set(x_29, 6, x_18);
lean_closure_set(x_29, 7, x_21);
x_30 = lean_array_get(x_10, x_28, x_20);
lean_dec(x_20);
lean_dec(x_28);
x_31 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__2), 8, 2);
lean_closure_set(x_31, 0, x_30);
lean_closure_set(x_31, 1, x_29);
x_32 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_23, x_31, x_2, x_3, x_4, x_5, x_6, x_15);
lean_dec(x_23);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_1);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_dec(x_12);
x_34 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1;
x_35 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_34, x_2, x_3, x_4, x_5, x_6, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_12);
if (x_36 == 0)
{
return x_12;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_12);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_8);
lean_dec(x_1);
x_42 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__2;
x_43 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_42, x_2, x_3, x_4, x_5, x_6, x_7);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Expr_getAppNumArgs(x_1);
x_11 = lean_nat_dec_lt(x_10, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_1);
x_12 = lean_apply_6(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_nat_sub(x_2, x_10);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_1, x_13, x_4, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_15, x_4, x_5, x_6, x_7, x_8, x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
x_14 = lean_nat_dec_lt(x_5, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_4, 1);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_11);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_16, 1, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_11);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
lean_dec(x_4);
x_29 = lean_ctor_get(x_19, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_31 = x_19;
} else {
 lean_dec_ref(x_19);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_16, 1, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_16);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_11);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_4);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_16, 1);
x_37 = lean_ctor_get(x_4, 0);
x_38 = lean_ctor_get(x_4, 1);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_37, 2);
lean_inc(x_47);
x_48 = lean_nat_dec_lt(x_46, x_47);
if (x_48 == 0)
{
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
lean_ctor_set(x_16, 0, x_44);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
uint8_t x_49; 
lean_free_object(x_18);
x_49 = !lean_is_exclusive(x_37);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_37, 2);
lean_dec(x_50);
x_51 = lean_ctor_get(x_37, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_37, 0);
lean_dec(x_52);
x_53 = lean_array_fget(x_45, x_46);
lean_inc(x_1);
x_54 = lean_array_get(x_1, x_2, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_55 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_43, x_53, x_54, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_46, x_60);
lean_dec(x_46);
lean_ctor_set(x_37, 1, x_61);
x_62 = l_Lean_Compiler_LCNF_joinTypes(x_58, x_42);
x_63 = lean_array_push(x_41, x_59);
lean_ctor_set(x_36, 1, x_62);
lean_ctor_set(x_36, 0, x_63);
lean_ctor_set(x_16, 0, x_44);
x_64 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_5 = x_64;
x_11 = x_57;
goto _start;
}
else
{
uint8_t x_66; 
lean_free_object(x_37);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_free_object(x_36);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_4);
lean_free_object(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_55);
if (x_66 == 0)
{
return x_55;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_55, 0);
x_68 = lean_ctor_get(x_55, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_55);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_37);
x_70 = lean_array_fget(x_45, x_46);
lean_inc(x_1);
x_71 = lean_array_get(x_1, x_2, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_72 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_43, x_70, x_71, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_add(x_46, x_77);
lean_dec(x_46);
x_79 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_79, 0, x_45);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_79, 2, x_47);
x_80 = l_Lean_Compiler_LCNF_joinTypes(x_75, x_42);
x_81 = lean_array_push(x_41, x_76);
lean_ctor_set(x_36, 1, x_80);
lean_ctor_set(x_36, 0, x_81);
lean_ctor_set(x_16, 0, x_44);
lean_ctor_set(x_4, 0, x_79);
x_82 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_5 = x_82;
x_11 = x_74;
goto _start;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_free_object(x_36);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_4);
lean_free_object(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_84 = lean_ctor_get(x_72, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_72, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_86 = x_72;
} else {
 lean_dec_ref(x_72);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_88 = lean_ctor_get(x_36, 0);
x_89 = lean_ctor_get(x_36, 1);
x_90 = lean_ctor_get(x_18, 0);
x_91 = lean_ctor_get(x_18, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_18);
x_92 = lean_ctor_get(x_37, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_37, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_37, 2);
lean_inc(x_94);
x_95 = lean_nat_dec_lt(x_93, x_94);
if (x_95 == 0)
{
lean_object* x_96; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
lean_ctor_set(x_16, 0, x_91);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_4);
lean_ctor_set(x_96, 1, x_11);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_97 = x_37;
} else {
 lean_dec_ref(x_37);
 x_97 = lean_box(0);
}
x_98 = lean_array_fget(x_92, x_93);
lean_inc(x_1);
x_99 = lean_array_get(x_1, x_2, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_100 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_90, x_98, x_99, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_add(x_93, x_105);
lean_dec(x_93);
if (lean_is_scalar(x_97)) {
 x_107 = lean_alloc_ctor(0, 3, 0);
} else {
 x_107 = x_97;
}
lean_ctor_set(x_107, 0, x_92);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_107, 2, x_94);
x_108 = l_Lean_Compiler_LCNF_joinTypes(x_103, x_89);
x_109 = lean_array_push(x_88, x_104);
lean_ctor_set(x_36, 1, x_108);
lean_ctor_set(x_36, 0, x_109);
lean_ctor_set(x_16, 0, x_91);
lean_ctor_set(x_4, 0, x_107);
x_110 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_5 = x_110;
x_11 = x_102;
goto _start;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_97);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_free_object(x_36);
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_4);
lean_free_object(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_112 = lean_ctor_get(x_100, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_100, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_114 = x_100;
} else {
 lean_dec_ref(x_100);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_116 = lean_ctor_get(x_36, 0);
x_117 = lean_ctor_get(x_36, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_36);
x_118 = lean_ctor_get(x_18, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_18, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_120 = x_18;
} else {
 lean_dec_ref(x_18);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_37, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_37, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_37, 2);
lean_inc(x_123);
x_124 = lean_nat_dec_lt(x_122, x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_118);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_116);
lean_ctor_set(x_125, 1, x_117);
lean_ctor_set(x_16, 1, x_125);
lean_ctor_set(x_16, 0, x_119);
if (lean_is_scalar(x_120)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_120;
 lean_ctor_set_tag(x_126, 0);
}
lean_ctor_set(x_126, 0, x_4);
lean_ctor_set(x_126, 1, x_11);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_120);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_127 = x_37;
} else {
 lean_dec_ref(x_37);
 x_127 = lean_box(0);
}
x_128 = lean_array_fget(x_121, x_122);
lean_inc(x_1);
x_129 = lean_array_get(x_1, x_2, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_130 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_118, x_128, x_129, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_nat_add(x_122, x_135);
lean_dec(x_122);
if (lean_is_scalar(x_127)) {
 x_137 = lean_alloc_ctor(0, 3, 0);
} else {
 x_137 = x_127;
}
lean_ctor_set(x_137, 0, x_121);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set(x_137, 2, x_123);
x_138 = l_Lean_Compiler_LCNF_joinTypes(x_133, x_117);
x_139 = lean_array_push(x_116, x_134);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
lean_ctor_set(x_16, 1, x_140);
lean_ctor_set(x_16, 0, x_119);
lean_ctor_set(x_4, 0, x_137);
x_141 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_5 = x_141;
x_11 = x_132;
goto _start;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_127);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_116);
lean_free_object(x_4);
lean_free_object(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_143 = lean_ctor_get(x_130, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_130, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_145 = x_130;
} else {
 lean_dec_ref(x_130);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_147 = lean_ctor_get(x_16, 1);
x_148 = lean_ctor_get(x_4, 0);
lean_inc(x_148);
lean_dec(x_4);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_151 = x_147;
} else {
 lean_dec_ref(x_147);
 x_151 = lean_box(0);
}
x_152 = lean_ctor_get(x_18, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_18, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_154 = x_18;
} else {
 lean_dec_ref(x_18);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_148, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_148, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_148, 2);
lean_inc(x_157);
x_158 = lean_nat_dec_lt(x_156, x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_152);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
if (lean_is_scalar(x_151)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_151;
}
lean_ctor_set(x_159, 0, x_149);
lean_ctor_set(x_159, 1, x_150);
lean_ctor_set(x_16, 1, x_159);
lean_ctor_set(x_16, 0, x_153);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_148);
lean_ctor_set(x_160, 1, x_16);
if (lean_is_scalar(x_154)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_154;
 lean_ctor_set_tag(x_161, 0);
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_11);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_154);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 lean_ctor_release(x_148, 2);
 x_162 = x_148;
} else {
 lean_dec_ref(x_148);
 x_162 = lean_box(0);
}
x_163 = lean_array_fget(x_155, x_156);
lean_inc(x_1);
x_164 = lean_array_get(x_1, x_2, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_165 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_152, x_163, x_164, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_dec(x_166);
x_170 = lean_unsigned_to_nat(1u);
x_171 = lean_nat_add(x_156, x_170);
lean_dec(x_156);
if (lean_is_scalar(x_162)) {
 x_172 = lean_alloc_ctor(0, 3, 0);
} else {
 x_172 = x_162;
}
lean_ctor_set(x_172, 0, x_155);
lean_ctor_set(x_172, 1, x_171);
lean_ctor_set(x_172, 2, x_157);
x_173 = l_Lean_Compiler_LCNF_joinTypes(x_168, x_150);
x_174 = lean_array_push(x_149, x_169);
if (lean_is_scalar(x_151)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_151;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_173);
lean_ctor_set(x_16, 1, x_175);
lean_ctor_set(x_16, 0, x_153);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_172);
lean_ctor_set(x_176, 1, x_16);
x_177 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_4 = x_176;
x_5 = x_177;
x_11 = x_167;
goto _start;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_162);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_free_object(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_179 = lean_ctor_get(x_165, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_165, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_181 = x_165;
} else {
 lean_dec_ref(x_165);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_16, 1);
x_184 = lean_ctor_get(x_16, 0);
lean_inc(x_183);
lean_inc(x_184);
lean_dec(x_16);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_185 = lean_ctor_get(x_4, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_186 = x_4;
} else {
 lean_dec_ref(x_4);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_183, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_183, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_189 = x_183;
} else {
 lean_dec_ref(x_183);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_184);
lean_ctor_set(x_191, 1, x_190);
if (lean_is_scalar(x_186)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_186;
}
lean_ctor_set(x_192, 0, x_185);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_11);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_194 = lean_ctor_get(x_4, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_195 = x_4;
} else {
 lean_dec_ref(x_4);
 x_195 = lean_box(0);
}
x_196 = lean_ctor_get(x_183, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_183, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_198 = x_183;
} else {
 lean_dec_ref(x_183);
 x_198 = lean_box(0);
}
x_199 = lean_ctor_get(x_184, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_184, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_201 = x_184;
} else {
 lean_dec_ref(x_184);
 x_201 = lean_box(0);
}
x_202 = lean_ctor_get(x_194, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_194, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_194, 2);
lean_inc(x_204);
x_205 = lean_nat_dec_lt(x_203, x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_199);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
if (lean_is_scalar(x_198)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_198;
}
lean_ctor_set(x_206, 0, x_196);
lean_ctor_set(x_206, 1, x_197);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_200);
lean_ctor_set(x_207, 1, x_206);
if (lean_is_scalar(x_195)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_195;
}
lean_ctor_set(x_208, 0, x_194);
lean_ctor_set(x_208, 1, x_207);
if (lean_is_scalar(x_201)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_201;
 lean_ctor_set_tag(x_209, 0);
}
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_11);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_201);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 x_210 = x_194;
} else {
 lean_dec_ref(x_194);
 x_210 = lean_box(0);
}
x_211 = lean_array_fget(x_202, x_203);
lean_inc(x_1);
x_212 = lean_array_get(x_1, x_2, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_213 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_199, x_211, x_212, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_214, 1);
lean_inc(x_217);
lean_dec(x_214);
x_218 = lean_unsigned_to_nat(1u);
x_219 = lean_nat_add(x_203, x_218);
lean_dec(x_203);
if (lean_is_scalar(x_210)) {
 x_220 = lean_alloc_ctor(0, 3, 0);
} else {
 x_220 = x_210;
}
lean_ctor_set(x_220, 0, x_202);
lean_ctor_set(x_220, 1, x_219);
lean_ctor_set(x_220, 2, x_204);
x_221 = l_Lean_Compiler_LCNF_joinTypes(x_216, x_197);
x_222 = lean_array_push(x_196, x_217);
if (lean_is_scalar(x_198)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_198;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_221);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_200);
lean_ctor_set(x_224, 1, x_223);
if (lean_is_scalar(x_195)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_195;
}
lean_ctor_set(x_225, 0, x_220);
lean_ctor_set(x_225, 1, x_224);
x_226 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_4 = x_225;
x_5 = x_226;
x_11 = x_215;
goto _start;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_210);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_200);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_228 = lean_ctor_get(x_213, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_213, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_230 = x_213;
} else {
 lean_dec_ref(x_213);
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsupported `", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` application during code generation", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitCases", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__2;
x_2 = lean_unsigned_to_nat(57u);
x_3 = lean_unsigned_to_nat(552u);
x_4 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__4;
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_13);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_9, x_10, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Compiler_LCNF_CasesInfo_numAlts(x_1);
x_20 = lean_nat_dec_eq(x_19, x_2);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_mk_empty_array_with_capacity(x_2);
if (lean_obj_tag(x_8) == 0)
{
x_22 = x_8;
goto block_162;
}
else
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_8, 0);
lean_inc(x_163);
x_22 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = l_Lean_instInhabitedExpr;
x_24 = lean_array_get(x_23, x_3, x_4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_25 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_24, x_10, x_11, x_12, x_13, x_14, x_18);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_22);
x_29 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0(x_22, x_10, x_11, x_12, x_13, x_14, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 5)
{
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_8);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_31, 4);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_ctor_get(x_5, 0);
lean_inc(x_36);
x_37 = lean_array_get_size(x_6);
x_38 = l_Array_toSubarray___redArg(x_6, x_2, x_37);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 0, x_21);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_25);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_41 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(x_23, x_3, x_5, x_40, x_36, x_10, x_11, x_12, x_13, x_14, x_32);
lean_dec(x_5);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
lean_inc(x_47);
x_48 = l_Lean_Compiler_LCNF_mkAuxParam(x_47, x_20, x_11, x_12, x_13, x_14, x_45);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
x_52 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_52, 0, x_22);
lean_ctor_set(x_52, 1, x_47);
lean_ctor_set(x_52, 2, x_34);
lean_ctor_set(x_52, 3, x_46);
lean_inc(x_50);
lean_ctor_set_tag(x_48, 3);
lean_ctor_set(x_48, 1, x_52);
x_53 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_48, x_10, x_51);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
lean_dec(x_50);
lean_ctor_set(x_27, 0, x_55);
x_56 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_27, x_3, x_7, x_10, x_11, x_12, x_13, x_14, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_48, 0);
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_48);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_22);
lean_ctor_set(x_59, 1, x_47);
lean_ctor_set(x_59, 2, x_34);
lean_ctor_set(x_59, 3, x_46);
lean_inc(x_57);
x_60 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_60, x_10, x_58);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
lean_dec(x_57);
lean_ctor_set(x_27, 0, x_63);
x_64 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_27, x_3, x_7, x_10, x_11, x_12, x_13, x_14, x_62);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_free_object(x_27);
lean_dec(x_34);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_65 = !lean_is_exclusive(x_41);
if (x_65 == 0)
{
return x_41;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_41, 0);
x_67 = lean_ctor_get(x_41, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_41);
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
x_69 = lean_ctor_get(x_27, 0);
lean_inc(x_69);
lean_dec(x_27);
x_70 = lean_ctor_get(x_31, 4);
lean_inc(x_70);
lean_dec(x_31);
x_71 = lean_ctor_get(x_5, 0);
lean_inc(x_71);
x_72 = lean_array_get_size(x_6);
x_73 = l_Array_toSubarray___redArg(x_6, x_2, x_72);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 0, x_21);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_25);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_76 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(x_23, x_3, x_5, x_75, x_71, x_10, x_11, x_12, x_13, x_14, x_32);
lean_dec(x_5);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_dec(x_76);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
lean_inc(x_82);
x_83 = l_Lean_Compiler_LCNF_mkAuxParam(x_82, x_20, x_11, x_12, x_13, x_14, x_80);
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
x_87 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_87, 0, x_22);
lean_ctor_set(x_87, 1, x_82);
lean_ctor_set(x_87, 2, x_69);
lean_ctor_set(x_87, 3, x_81);
lean_inc(x_84);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(3, 2, 0);
} else {
 x_88 = x_86;
 lean_ctor_set_tag(x_88, 3);
}
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_88, x_10, x_85);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = lean_ctor_get(x_84, 0);
lean_inc(x_91);
lean_dec(x_84);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_92, x_3, x_7, x_10, x_11, x_12, x_13, x_14, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_69);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_94 = lean_ctor_get(x_76, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_76, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_96 = x_76;
} else {
 lean_dec_ref(x_76);
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
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_98 = lean_ctor_get(x_29, 1);
lean_inc(x_98);
lean_dec(x_29);
x_99 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__1;
x_100 = l_Lean_MessageData_ofName(x_8);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_100);
lean_ctor_set(x_25, 0, x_99);
x_101 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__3;
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_25);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(x_102, x_12, x_13, x_14, x_98);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_30);
lean_free_object(x_25);
lean_dec(x_27);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_104 = lean_ctor_get(x_29, 1);
lean_inc(x_104);
lean_dec(x_29);
x_105 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__5;
x_106 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_105, x_10, x_11, x_12, x_13, x_14, x_104);
return x_106;
}
}
else
{
uint8_t x_107; 
lean_free_object(x_25);
lean_dec(x_27);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_107 = !lean_is_exclusive(x_29);
if (x_107 == 0)
{
return x_29;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_29, 0);
x_109 = lean_ctor_get(x_29, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_29);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_25, 0);
x_112 = lean_ctor_get(x_25, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_25);
lean_inc(x_22);
x_113 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0(x_22, x_10, x_11, x_12, x_13, x_14, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
if (lean_obj_tag(x_114) == 5)
{
if (lean_obj_tag(x_111) == 1)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_8);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_117 = lean_ctor_get(x_111, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_118 = x_111;
} else {
 lean_dec_ref(x_111);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_115, 4);
lean_inc(x_119);
lean_dec(x_115);
x_120 = lean_ctor_get(x_5, 0);
lean_inc(x_120);
x_121 = lean_array_get_size(x_6);
x_122 = l_Array_toSubarray___redArg(x_6, x_2, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_21);
lean_ctor_set(x_123, 1, x_17);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_119);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_124);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_126 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(x_23, x_3, x_5, x_125, x_120, x_10, x_11, x_12, x_13, x_14, x_116);
lean_dec(x_5);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_ctor_get(x_126, 1);
lean_inc(x_130);
lean_dec(x_126);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
lean_inc(x_132);
x_133 = l_Lean_Compiler_LCNF_mkAuxParam(x_132, x_20, x_11, x_12, x_13, x_14, x_130);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
x_137 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_137, 0, x_22);
lean_ctor_set(x_137, 1, x_132);
lean_ctor_set(x_137, 2, x_117);
lean_ctor_set(x_137, 3, x_131);
lean_inc(x_134);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(3, 2, 0);
} else {
 x_138 = x_136;
 lean_ctor_set_tag(x_138, 3);
}
lean_ctor_set(x_138, 0, x_134);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_138, x_10, x_135);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_ctor_get(x_134, 0);
lean_inc(x_141);
lean_dec(x_134);
if (lean_is_scalar(x_118)) {
 x_142 = lean_alloc_ctor(1, 1, 0);
} else {
 x_142 = x_118;
}
lean_ctor_set(x_142, 0, x_141);
x_143 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_142, x_3, x_7, x_10, x_11, x_12, x_13, x_14, x_140);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_144 = lean_ctor_get(x_126, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_126, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_146 = x_126;
} else {
 lean_dec_ref(x_126);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_114);
lean_dec(x_111);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_148 = lean_ctor_get(x_113, 1);
lean_inc(x_148);
lean_dec(x_113);
x_149 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__1;
x_150 = l_Lean_MessageData_ofName(x_8);
x_151 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__3;
x_153 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(x_153, x_12, x_13, x_14, x_148);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_114);
lean_dec(x_111);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_155 = lean_ctor_get(x_113, 1);
lean_inc(x_155);
lean_dec(x_113);
x_156 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__5;
x_157 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_156, x_10, x_11, x_12, x_13, x_14, x_155);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_111);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_158 = lean_ctor_get(x_113, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_113, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_160 = x_113;
} else {
 lean_dec_ref(x_113);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
}
else
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_25;
}
}
}
else
{
lean_object* x_164; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_164 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_17, x_10, x_11, x_12, x_13, x_14, x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_164;
}
}
else
{
uint8_t x_165; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_165 = !lean_is_exclusive(x_16);
if (x_165 == 0)
{
return x_16;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_16, 0);
x_167 = lean_ctor_get(x_16, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_16);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; 
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__1;
x_15 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__2;
x_16 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__3;
x_17 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__4;
x_18 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__5;
x_19 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__6;
lean_inc_n(x_1, 3);
x_20 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_1);
lean_ctor_set(x_20, 2, x_1);
lean_ctor_set(x_20, 3, x_14);
lean_ctor_set(x_20, 4, x_15);
lean_ctor_set(x_20, 5, x_16);
lean_ctor_set(x_20, 6, x_17);
lean_ctor_set(x_20, 7, x_18);
lean_ctor_set(x_20, 8, x_19);
x_21 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__4;
x_22 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5;
x_23 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__6;
x_24 = 5;
lean_inc_n(x_1, 2);
x_25 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_1);
lean_ctor_set(x_25, 3, x_1);
lean_ctor_set_usize(x_25, 4, x_24);
x_26 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__9;
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_13);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_st_mk_ref(x_27, x_12);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
lean_dec(x_11);
x_32 = lean_box(0);
x_33 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_34 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_35 = lean_mk_empty_array_with_capacity(x_1);
x_36 = lean_box(0);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_13);
lean_ctor_set(x_38, 2, x_31);
lean_ctor_set(x_38, 3, x_35);
lean_ctor_set(x_38, 4, x_36);
lean_ctor_set(x_38, 5, x_1);
lean_ctor_set(x_38, 6, x_37);
lean_ctor_set_uint64(x_38, sizeof(void*)*7, x_34);
x_39 = lean_unbox(x_32);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 8, x_39);
x_40 = lean_unbox(x_32);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 9, x_40);
x_41 = lean_unbox(x_32);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 10, x_41);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_29);
x_42 = lean_infer_type(x_2, x_38, x_29, x_7, x_8, x_30);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_st_ref_get(x_29, x_44);
lean_dec(x_29);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_apply_7(x_3, x_43, x_4, x_5, x_6, x_7, x_8, x_46);
return x_47;
}
else
{
lean_dec(x_29);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_dec(x_42);
x_50 = lean_apply_7(x_3, x_48, x_4, x_5, x_6, x_7, x_8, x_49);
return x_50;
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
x_51 = !lean_is_exclusive(x_42);
if (x_51 == 0)
{
return x_42;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_42, 0);
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_42);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 5);
lean_inc(x_13);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__27;
x_15 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_15);
x_16 = lean_mk_array(x_15, x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_15, x_17);
lean_dec(x_15);
lean_inc(x_2);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_16, x_18);
x_20 = l_Lean_Expr_getAppFn(x_2);
x_21 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___boxed), 15, 8);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_21);
lean_closure_set(x_22, 2, x_19);
lean_closure_set(x_22, 3, x_11);
lean_closure_set(x_22, 4, x_12);
lean_closure_set(x_22, 5, x_13);
lean_closure_set(x_22, 6, x_10);
lean_closure_set(x_22, 7, x_9);
lean_inc(x_10);
x_23 = l_Array_toSubarray___redArg(x_19, x_21, x_10);
x_24 = l_Array_ofSubarray___redArg(x_23);
lean_dec(x_23);
x_25 = l_Lean_mkAppN(x_20, x_24);
lean_dec(x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1), 9, 3);
lean_closure_set(x_26, 0, x_21);
lean_closure_set(x_26, 1, x_25);
lean_closure_set(x_26, 2, x_22);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_2, x_10, x_26, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_nat_dec_lt(x_4, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_1, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_15, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_push(x_3, x_17);
x_20 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_3 = x_19;
x_4 = x_20;
x_10 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_eq(x_10, x_3);
if (x_11 == 0)
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___closed__0;
x_15 = lean_unsigned_to_nat(1u);
lean_inc(x_3);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg(x_2, x_16, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
x_22 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_20, x_21, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_4);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
default: 
{
lean_object* x_27; lean_object* x_28; 
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
lean_ctor_set(x_28, 1, x_9);
return x_28;
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_9);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_uget(x_3, x_2);
lean_inc(x_12);
x_13 = l_Lean_Compiler_LCNF_Param_toExpr(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Compiler_LCNF_inferType(x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_7);
x_17 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_15, x_4, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_37; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = lean_array_uset(x_3, x_2, x_20);
x_37 = lean_unbox(x_18);
lean_dec(x_18);
if (x_37 == 0)
{
lean_inc(x_6);
x_22 = x_4;
x_23 = x_6;
x_24 = x_19;
goto block_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_st_ref_take(x_4, x_19);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_39, 5);
x_43 = lean_ctor_get(x_12, 0);
lean_inc(x_43);
x_44 = l_Lean_FVarIdSet_insert(x_42, x_43);
lean_ctor_set(x_39, 5, x_44);
x_45 = lean_st_ref_set(x_4, x_39, x_40);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
lean_inc(x_6);
x_22 = x_4;
x_23 = x_6;
x_24 = x_46;
goto block_36;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_47 = lean_ctor_get(x_39, 0);
x_48 = lean_ctor_get(x_39, 1);
x_49 = lean_ctor_get(x_39, 2);
x_50 = lean_ctor_get(x_39, 3);
x_51 = lean_ctor_get(x_39, 4);
x_52 = lean_ctor_get(x_39, 5);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_39);
x_53 = lean_ctor_get(x_12, 0);
lean_inc(x_53);
x_54 = l_Lean_FVarIdSet_insert(x_52, x_53);
x_55 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_48);
lean_ctor_set(x_55, 2, x_49);
lean_ctor_set(x_55, 3, x_50);
lean_ctor_set(x_55, 4, x_51);
lean_ctor_set(x_55, 5, x_54);
x_56 = lean_st_ref_set(x_4, x_55, x_40);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
lean_inc(x_6);
x_22 = x_4;
x_23 = x_6;
x_24 = x_57;
goto block_36;
}
}
block_36:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_12, 2);
lean_inc(x_25);
x_26 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(x_25, x_22, x_24);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(x_12, x_27, x_23, x_28);
lean_dec(x_23);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = 1;
x_33 = lean_usize_add(x_2, x_32);
x_34 = lean_array_uset(x_21, x_2, x_30);
x_2 = x_33;
x_3 = x_34;
x_9 = x_31;
goto _start;
}
}
else
{
uint8_t x_58; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_17);
if (x_58 == 0)
{
return x_17;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_17, 0);
x_60 = lean_ctor_get(x_17, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_17);
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
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_14);
if (x_62 == 0)
{
return x_14;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_14, 0);
x_64 = lean_ctor_get(x_14, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_14);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_56; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_56 = l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_array_get_size(x_59);
x_62 = lean_nat_dec_lt(x_61, x_2);
if (x_62 == 0)
{
lean_dec(x_61);
lean_dec(x_2);
x_10 = x_60;
x_11 = x_59;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = x_8;
x_17 = x_58;
goto block_55;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_nat_sub(x_2, x_61);
lean_dec(x_61);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
x_64 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_60, x_63, x_4, x_7, x_8, x_58);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_8);
lean_inc(x_7);
x_67 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda(x_65, x_4, x_5, x_6, x_7, x_8, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = l_Array_append___redArg(x_59, x_70);
lean_dec(x_70);
x_10 = x_71;
x_11 = x_72;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = x_8;
x_17 = x_69;
goto block_55;
}
else
{
uint8_t x_73; 
lean_dec(x_59);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_67);
if (x_73 == 0)
{
return x_67;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_67, 0);
x_75 = lean_ctor_get(x_67, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_67);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_59);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_64);
if (x_77 == 0)
{
return x_64;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_64, 0);
x_79 = lean_ctor_get(x_64, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_64);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_56);
if (x_81 == 0)
{
return x_56;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_56, 0);
x_83 = lean_ctor_get(x_56, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_56);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
block_55:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_array_size(x_11);
x_19 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_20 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__0(x_18, x_19, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_23 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_10, x_12, x_13, x_14, x_15, x_16, x_22);
if (lean_obj_tag(x_23) == 0)
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
x_26 = l_Lean_Compiler_LCNF_ToLCNF_toCode(x_24, x_12, x_13, x_14, x_15, x_16, x_25);
lean_dec(x_12);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_27);
x_29 = l_Lean_Compiler_LCNF_Code_inferType(x_27, x_13, x_14, x_15, x_16, x_28);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_27);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_21);
lean_ctor_set(x_36, 2, x_27);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_29);
if (x_39 == 0)
{
return x_29;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_29, 0);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_29);
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
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_26);
if (x_43 == 0)
{
return x_26;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_26, 0);
x_45 = lean_ctor_get(x_26, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_26);
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
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_23);
if (x_47 == 0)
{
return x_23;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_23, 0);
x_49 = lean_ctor_get(x_23, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_23);
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
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_20);
if (x_51 == 0)
{
return x_20;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_20, 0);
x_53 = lean_ctor_get(x_20, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_20);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lam__0), 9, 3);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_1);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg(x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_1, x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_9, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_15 = lean_st_mk_ref(x_14, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_box(0);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_21 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_22 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13;
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set(x_25, 5, x_13);
lean_ctor_set(x_25, 6, x_24);
lean_ctor_set_uint64(x_25, sizeof(void*)*7, x_21);
x_26 = lean_unbox(x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 8, x_26);
x_27 = lean_unbox(x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 9, x_27);
x_28 = lean_unbox(x_19);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 10, x_28);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_16);
x_29 = lean_infer_type(x_1, x_25, x_16, x_6, x_7, x_17);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_st_ref_get(x_16, x_31);
lean_dec(x_16);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_apply_7(x_2, x_30, x_3, x_4, x_5, x_6, x_7, x_33);
return x_34;
}
else
{
lean_dec(x_16);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_apply_7(x_2, x_35, x_3, x_4, x_5, x_6, x_7, x_36);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
return x_29;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_29);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__0___boxed), 7, 0);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__1), 8, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_10, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_9 = l_Lean_instInhabitedExpr;
x_10 = lean_unsigned_to_nat(5u);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__27;
x_12 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_12);
x_13 = lean_mk_array(x_12, x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_12, x_14);
lean_dec(x_12);
lean_inc(x_1);
x_16 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_13, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get(x_9, x_16, x_17);
x_19 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(x_18);
x_20 = lean_array_get(x_9, x_16, x_14);
x_21 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(x_20);
x_22 = lean_array_get(x_9, x_16, x_2);
x_23 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___closed__0;
x_24 = lean_array_push(x_23, x_19);
x_25 = lean_array_push(x_24, x_21);
x_26 = l_Lean_Expr_beta(x_22, x_25);
x_27 = lean_array_get_size(x_16);
x_28 = l_Array_toSubarray___redArg(x_16, x_10, x_27);
x_29 = l_Array_ofSubarray___redArg(x_28);
lean_dec(x_28);
x_30 = l_Lean_mkAppN(x_26, x_29);
lean_dec(x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 7, 1);
lean_closure_set(x_31, 0, x_30);
x_32 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_10, x_31, x_3, x_4, x_5, x_6, x_7, x_8);
return x_32;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_19; lean_object* x_27; uint8_t x_28; 
x_8 = lean_unsigned_to_nat(7u);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__27;
x_10 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_10);
x_11 = lean_mk_array(x_10, x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_10, x_12);
lean_dec(x_10);
lean_inc(x_1);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_11, x_13);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13;
x_28 = l_Lean_Expr_isAppOf(x_1, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__14;
x_30 = l_Lean_Expr_isAppOf(x_1, x_29);
x_19 = x_30;
goto block_26;
}
else
{
x_19 = x_28;
goto block_26;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0___boxed), 9, 3);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_8);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_8, x_16, x_2, x_3, x_4, x_5, x_6, x_7);
return x_17;
}
block_26:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_instInhabitedExpr;
x_21 = lean_unsigned_to_nat(6u);
x_22 = lean_array_get(x_20, x_14, x_21);
x_15 = x_22;
goto block_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = l_Lean_instInhabitedExpr;
x_24 = lean_unsigned_to_nat(3u);
x_25 = lean_array_get(x_23, x_14, x_24);
x_15 = x_25;
goto block_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_19; lean_object* x_27; uint8_t x_28; 
x_8 = lean_unsigned_to_nat(6u);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__27;
x_10 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_10);
x_11 = lean_mk_array(x_10, x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_10, x_12);
lean_dec(x_10);
lean_inc(x_1);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_11, x_13);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8;
x_28 = l_Lean_Expr_isAppOf(x_1, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2;
x_30 = l_Lean_Expr_isAppOf(x_1, x_29);
x_19 = x_30;
goto block_26;
}
else
{
x_19 = x_28;
goto block_26;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0___boxed), 9, 3);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_8);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_8, x_16, x_2, x_3, x_4, x_5, x_6, x_7);
return x_17;
}
block_26:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_instInhabitedExpr;
x_21 = lean_unsigned_to_nat(5u);
x_22 = lean_array_get(x_20, x_14, x_21);
x_15 = x_22;
goto block_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = l_Lean_instInhabitedExpr;
x_24 = lean_unsigned_to_nat(3u);
x_25 = lean_array_get(x_23, x_14, x_24);
x_15 = x_25;
goto block_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = l_Lean_Expr_getAppFn(x_2);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__27;
x_11 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_11);
x_12 = lean_mk_array(x_11, x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_11, x_13);
lean_dec(x_11);
lean_inc(x_2);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_12, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst), 8, 2);
lean_closure_set(x_16, 0, x_9);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_2, x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitQuotLift", 46, 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__2;
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_unsigned_to_nat(583u);
x_4 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__0;
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lcInv", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__2;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__2;
x_2 = lean_unsigned_to_nat(19u);
x_3 = lean_unsigned_to_nat(587u);
x_4 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__0;
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_1, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(5u);
x_20 = lean_array_get(x_2, x_3, x_19);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_21 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_20, x_10, x_11, x_12, x_13, x_14, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_32; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_32 = l_Lean_Expr_getAppFn(x_4);
if (lean_obj_tag(x_32) == 4)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_24 = x_10;
x_25 = x_11;
x_26 = x_12;
x_27 = x_13;
x_28 = x_14;
goto block_31;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_dec(x_33);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_24 = x_10;
x_25 = x_11;
x_26 = x_12;
x_27 = x_13;
x_28 = x_14;
goto block_31;
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 1);
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_dec(x_40);
x_41 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__3;
lean_ctor_set(x_34, 0, x_39);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_5);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_6);
x_44 = lean_mk_empty_array_with_capacity(x_7);
x_45 = lean_array_push(x_44, x_42);
x_46 = lean_array_push(x_45, x_43);
x_47 = lean_array_push(x_46, x_22);
x_48 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_34);
lean_ctor_set(x_48, 2, x_47);
x_49 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_50 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_48, x_49, x_10, x_11, x_12, x_13, x_14, x_23);
if (lean_obj_tag(x_50) == 0)
{
switch (lean_obj_tag(x_17)) {
case 0:
{
uint8_t x_51; 
lean_free_object(x_33);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_17);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_17);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
case 1:
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_dec(x_50);
x_57 = !lean_is_exclusive(x_17);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_17, 0, x_55);
x_59 = lean_mk_empty_array_with_capacity(x_8);
x_60 = lean_array_push(x_59, x_17);
lean_ctor_set_tag(x_33, 4);
lean_ctor_set(x_33, 1, x_60);
lean_ctor_set(x_33, 0, x_58);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_61 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_33, x_49, x_10, x_11, x_12, x_13, x_14, x_56);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_62, x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_63);
return x_64;
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_61;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_17, 0);
lean_inc(x_65);
lean_dec(x_17);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_55);
x_67 = lean_mk_empty_array_with_capacity(x_8);
x_68 = lean_array_push(x_67, x_66);
lean_ctor_set_tag(x_33, 4);
lean_ctor_set(x_33, 1, x_68);
lean_ctor_set(x_33, 0, x_65);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_69 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_33, x_49, x_10, x_11, x_12, x_13, x_14, x_56);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_70, x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_71);
return x_72;
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_69;
}
}
}
default: 
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_free_object(x_33);
lean_dec(x_17);
lean_dec(x_9);
x_73 = lean_ctor_get(x_50, 1);
lean_inc(x_73);
lean_dec(x_50);
x_74 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__4;
x_75 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_74, x_10, x_11, x_12, x_13, x_14, x_73);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_free_object(x_33);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_76 = !lean_is_exclusive(x_50);
if (x_76 == 0)
{
return x_50;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_50, 0);
x_78 = lean_ctor_get(x_50, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_50);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_80 = lean_ctor_get(x_33, 0);
lean_inc(x_80);
lean_dec(x_33);
x_81 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__3;
lean_ctor_set(x_34, 0, x_80);
x_82 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_82, 0, x_5);
x_83 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_83, 0, x_6);
x_84 = lean_mk_empty_array_with_capacity(x_7);
x_85 = lean_array_push(x_84, x_82);
x_86 = lean_array_push(x_85, x_83);
x_87 = lean_array_push(x_86, x_22);
x_88 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_88, 0, x_81);
lean_ctor_set(x_88, 1, x_34);
lean_ctor_set(x_88, 2, x_87);
x_89 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_90 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_88, x_89, x_10, x_11, x_12, x_13, x_14, x_23);
if (lean_obj_tag(x_90) == 0)
{
switch (lean_obj_tag(x_17)) {
case 0:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_17);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
case 1:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
lean_dec(x_90);
x_96 = lean_ctor_get(x_17, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_97 = x_17;
} else {
 lean_dec_ref(x_17);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_94);
x_99 = lean_mk_empty_array_with_capacity(x_8);
x_100 = lean_array_push(x_99, x_98);
x_101 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_100);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_102 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_101, x_89, x_10, x_11, x_12, x_13, x_14, x_95);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_103, x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_104);
return x_105;
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_102;
}
}
default: 
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_17);
lean_dec(x_9);
x_106 = lean_ctor_get(x_90, 1);
lean_inc(x_106);
lean_dec(x_90);
x_107 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__4;
x_108 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_107, x_10, x_11, x_12, x_13, x_14, x_106);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_109 = lean_ctor_get(x_90, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_90, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_111 = x_90;
} else {
 lean_dec_ref(x_90);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
else
{
lean_free_object(x_34);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_24 = x_10;
x_25 = x_11;
x_26 = x_12;
x_27 = x_13;
x_28 = x_14;
goto block_31;
}
}
else
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_34, 1);
lean_inc(x_113);
lean_dec(x_34);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_114 = lean_ctor_get(x_33, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_115 = x_33;
} else {
 lean_dec_ref(x_33);
 x_115 = lean_box(0);
}
x_116 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__3;
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_113);
x_118 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_118, 0, x_5);
x_119 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_119, 0, x_6);
x_120 = lean_mk_empty_array_with_capacity(x_7);
x_121 = lean_array_push(x_120, x_118);
x_122 = lean_array_push(x_121, x_119);
x_123 = lean_array_push(x_122, x_22);
x_124 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_124, 0, x_116);
lean_ctor_set(x_124, 1, x_117);
lean_ctor_set(x_124, 2, x_123);
x_125 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_126 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_124, x_125, x_10, x_11, x_12, x_13, x_14, x_23);
if (lean_obj_tag(x_126) == 0)
{
switch (lean_obj_tag(x_17)) {
case 0:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_115);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_128 = x_126;
} else {
 lean_dec_ref(x_126);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_17);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
case 1:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_130 = lean_ctor_get(x_126, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_126, 1);
lean_inc(x_131);
lean_dec(x_126);
x_132 = lean_ctor_get(x_17, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_133 = x_17;
} else {
 lean_dec_ref(x_17);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 1, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_130);
x_135 = lean_mk_empty_array_with_capacity(x_8);
x_136 = lean_array_push(x_135, x_134);
if (lean_is_scalar(x_115)) {
 x_137 = lean_alloc_ctor(4, 2, 0);
} else {
 x_137 = x_115;
 lean_ctor_set_tag(x_137, 4);
}
lean_ctor_set(x_137, 0, x_132);
lean_ctor_set(x_137, 1, x_136);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_138 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_137, x_125, x_10, x_11, x_12, x_13, x_14, x_131);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_139, x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_140);
return x_141;
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_138;
}
}
default: 
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_115);
lean_dec(x_17);
lean_dec(x_9);
x_142 = lean_ctor_get(x_126, 1);
lean_inc(x_142);
lean_dec(x_126);
x_143 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__4;
x_144 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_143, x_10, x_11, x_12, x_13, x_14, x_142);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_115);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_145 = lean_ctor_get(x_126, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_126, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_147 = x_126;
} else {
 lean_dec_ref(x_126);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
lean_dec(x_113);
lean_dec(x_33);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_24 = x_10;
x_25 = x_11;
x_26 = x_12;
x_27 = x_13;
x_28 = x_14;
goto block_31;
}
}
}
}
}
else
{
lean_dec(x_32);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_24 = x_10;
x_25 = x_11;
x_26 = x_12;
x_27 = x_13;
x_28 = x_14;
goto block_31;
}
block_31:
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__1;
x_30 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(x_29, x_24, x_25, x_26, x_27, x_28, x_23);
return x_30;
}
}
else
{
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_21;
}
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = l_Lean_instInhabitedExpr;
x_9 = lean_unsigned_to_nat(6u);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__27;
x_11 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_11);
x_12 = lean_mk_array(x_11, x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_11, x_13);
lean_dec(x_11);
lean_inc(x_1);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_12, x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get(x_8, x_15, x_16);
x_18 = lean_array_get(x_8, x_15, x_13);
x_19 = lean_unsigned_to_nat(3u);
x_20 = lean_array_get(x_8, x_15, x_19);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___boxed), 15, 9);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_8);
lean_closure_set(x_21, 2, x_15);
lean_closure_set(x_21, 3, x_1);
lean_closure_set(x_21, 4, x_17);
lean_closure_set(x_21, 5, x_18);
lean_closure_set(x_21, 6, x_19);
lean_closure_set(x_21, 7, x_13);
lean_closure_set(x_21, 8, x_9);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_9, x_21, x_2, x_3, x_4, x_5, x_6, x_7);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__0(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_toCode(x_9, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_2);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF___lam__0), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* initialize_Lean_ProjFns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_BorrowedAnnotation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_CSimpAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ToLCNF(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ProjFns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CtorRecognizer(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_BorrowedAnnotation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_CSimpAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ImplementedByAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Bind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__4 = _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__4);
l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__5 = _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__5);
l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__6 = _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__6);
l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement = _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement);
l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__0 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__0();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__0);
l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__1 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__1();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__1);
l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__2 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__2();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__2);
l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__3 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__3();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__3);
l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__4 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__4();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__4);
l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__5 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__5();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__5);
l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__6 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__6();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__6);
l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__7 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__7();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___closed__7);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__10 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__10);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__13 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__13);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__14 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__14);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__16 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__16);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__4 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__4);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__6 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__6);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__7 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__7);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__8 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__8);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__9 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__9);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12();
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__13);
l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__4 = _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__4);
l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__5 = _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__5);
l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__6 = _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__6);
l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__7 = _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__7);
l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__8 = _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__8);
l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__9 = _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__9);
l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__10 = _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__10);
l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_visitLambda___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_visitLambda___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_visitLambda___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2);
l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__0 = _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__0();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__0);
l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__1 = _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__1();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__1);
l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__2 = _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__2();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__2);
l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__3 = _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__3();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__3);
l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__4 = _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__4();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___closed__4);
l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__0 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__0);
l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__1);
l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__2);
l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__3);
l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__4);
l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__5);
l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___closed__6);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__14 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__14);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__16 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__16);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__18 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__18);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__19 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__19();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__19);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__20 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__20();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__20);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__21 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__21();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__21);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__23 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__23();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__23);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__24 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__24();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__24);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__25 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__25();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__25);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__26 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__26();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__26);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__27 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__27();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__27);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1);
l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__0 = _init_l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__0();
lean_mark_persistent(l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__0);
l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__1 = _init_l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__1();
lean_mark_persistent(l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__1);
l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__2 = _init_l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__2();
lean_mark_persistent(l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__2);
l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__3 = _init_l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__3();
lean_mark_persistent(l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__4 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__4);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__5 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__5);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__4 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
