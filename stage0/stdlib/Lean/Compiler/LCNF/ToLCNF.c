// Lean compiler output
// Module: Lean.Compiler.LCNF.ToLCNF
// Imports: Lean.ProjFns Lean.Meta.CtorRecognizer Lean.Compiler.BorrowedAnnotation Lean.Compiler.CSimpAttr Lean.Compiler.ImplementedByAttr Lean.Compiler.LCNF.Types Lean.Compiler.LCNF.Bind Lean.Compiler.LCNF.InferType Lean.Compiler.LCNF.Util Lean.Compiler.NeverExtractAttr
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
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__3;
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_litToValue(lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__1;
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__26;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13;
lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0_spec__0___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7;
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__3;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__2;
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__24;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1;
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__0;
extern lean_object* l_Lean_unknownIdentifierMessageTag;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__21;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__27;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__14;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__5;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__14;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__9;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__0;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2;
lean_object* l_Lean_Compiler_LCNF_getBinderName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__5___redArg___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_411_(uint8_t, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__4;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__2;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_isLCProof(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__1;
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__4;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__3;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Std_Iterators_instIteratorMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__8;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__0;
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getCtorArity_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__23;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__2;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__5___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__4___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__8;
lean_object* l_Lean_Compiler_LCNF_joinTypes(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Std_Iterators_Types_Attach_instIterator___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isPredicateType(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__20;
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isMarkedBorrowed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_CSimp_replaceConstants(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___closed__0;
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isRuntimeBuiltinType(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__18;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__5;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9;
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t lean_is_no_confusion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__22;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__28;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2;
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5___redArg(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__18;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__3;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__17;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12;
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__13;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__4;
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___closed__0;
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__0;
lean_object* l_Lean_Compiler_LCNF_CasesInfo_numAlts(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__0;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__10;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557_(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6;
uint8_t l_Lean_BinderInfo_isImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__10;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3;
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PRange_instUpwardEnumerableNat;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(lean_object*, lean_object*);
lean_object* l_Lean_Expr_toCtorIfLit(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__19;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__4;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__16;
lean_object* l_Lean_Compiler_LCNF_getCasesInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5;
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__0;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__0;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__0;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1;
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___boxed(lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___closed__0;
lean_object* l_Lean_Compiler_LCNF_mkParam(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_FVarIdSet_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__21;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1___redArg(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__2;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__3;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lam__2(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
static lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__0;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1;
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__9;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__5;
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Compiler_LCNF_anyExpr;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Param_toExpr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1;
lean_object* l_Lean_Compiler_LCNF_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__0;
static lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__5;
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PRange_instIteratorRangeIteratorIdOfUpwardEnumerableOfSupportsUpperBound___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__0;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10;
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3_spec__3_spec__3___redArg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lam__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1;
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__25;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__20;
static lean_object* l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8;
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__6;
lean_object* lean_get_projection_info(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__6;
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__16;
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_hasNeverExtractAttribute_visit(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__19;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__5;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__2;
static lean_object* l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_4);
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
lean_dec_ref(x_8);
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
lean_inc_ref(x_18);
lean_dec_ref(x_13);
x_19 = lean_array_get_size(x_18);
lean_dec_ref(x_18);
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
lean_inc_ref(x_25);
lean_dec_ref(x_13);
x_26 = lean_array_get_size(x_25);
lean_dec_ref(x_25);
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
lean_dec_ref(x_5);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = l_Lean_Name_quickCmp(x_2, x_3);
switch (x_7) {
case 0:
{
x_1 = x_5;
goto _start;
}
case 1:
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
default: 
{
x_1 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_8 = l_Lean_Name_quickCmp(x_1, x_3);
switch (x_8) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_1, x_5);
x_10 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_9) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 4);
lean_inc(x_16);
x_17 = lean_unsigned_to_nat(3u);
x_18 = lean_nat_mul(x_17, x_11);
x_19 = lean_nat_dec_lt(x_18, x_12);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_20 = lean_nat_add(x_10, x_11);
lean_dec(x_11);
x_21 = lean_nat_add(x_20, x_12);
lean_dec(x_12);
lean_dec(x_20);
if (lean_is_scalar(x_7)) {
 x_22 = lean_alloc_ctor(0, 5, 0);
} else {
 x_22 = x_7;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_4);
lean_ctor_set(x_22, 3, x_9);
lean_ctor_set(x_22, 4, x_6);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_23 = x_6;
} else {
 lean_dec_ref(x_6);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_15, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_15, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_15, 4);
lean_inc(x_28);
x_29 = lean_ctor_get(x_16, 0);
lean_inc(x_29);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_mul(x_30, x_29);
x_32 = lean_nat_dec_lt(x_24, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_43; 
lean_dec(x_24);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 lean_ctor_release(x_15, 4);
 x_33 = x_15;
} else {
 lean_dec_ref(x_15);
 x_33 = lean_box(0);
}
x_34 = lean_nat_add(x_10, x_11);
lean_dec(x_11);
x_35 = lean_nat_add(x_34, x_12);
lean_dec(x_12);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_27, 0);
lean_inc(x_50);
x_43 = x_50;
goto block_49;
}
else
{
lean_object* x_51; 
x_51 = lean_unsigned_to_nat(0u);
x_43 = x_51;
goto block_49;
}
block_42:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_nat_add(x_36, x_38);
lean_dec(x_38);
lean_dec(x_36);
if (lean_is_scalar(x_33)) {
 x_40 = lean_alloc_ctor(0, 5, 0);
} else {
 x_40 = x_33;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_13);
lean_ctor_set(x_40, 2, x_14);
lean_ctor_set(x_40, 3, x_28);
lean_ctor_set(x_40, 4, x_16);
if (lean_is_scalar(x_23)) {
 x_41 = lean_alloc_ctor(0, 5, 0);
} else {
 x_41 = x_23;
}
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_25);
lean_ctor_set(x_41, 2, x_26);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 4, x_40);
return x_41;
}
block_49:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_nat_add(x_34, x_43);
lean_dec(x_43);
lean_dec(x_34);
if (lean_is_scalar(x_7)) {
 x_45 = lean_alloc_ctor(0, 5, 0);
} else {
 x_45 = x_7;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_3);
lean_ctor_set(x_45, 2, x_4);
lean_ctor_set(x_45, 3, x_9);
lean_ctor_set(x_45, 4, x_27);
x_46 = lean_nat_add(x_10, x_29);
lean_dec(x_29);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_28, 0);
lean_inc(x_47);
x_36 = x_46;
x_37 = x_45;
x_38 = x_47;
goto block_42;
}
else
{
lean_object* x_48; 
x_48 = lean_unsigned_to_nat(0u);
x_36 = x_46;
x_37 = x_45;
x_38 = x_48;
goto block_42;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_7);
x_52 = lean_nat_add(x_10, x_11);
lean_dec(x_11);
x_53 = lean_nat_add(x_52, x_12);
lean_dec(x_12);
x_54 = lean_nat_add(x_52, x_24);
lean_dec(x_24);
lean_dec(x_52);
lean_inc_ref(x_9);
if (lean_is_scalar(x_23)) {
 x_55 = lean_alloc_ctor(0, 5, 0);
} else {
 x_55 = x_23;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_3);
lean_ctor_set(x_55, 2, x_4);
lean_ctor_set(x_55, 3, x_9);
lean_ctor_set(x_55, 4, x_15);
x_56 = !lean_is_exclusive(x_9);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_9, 4);
lean_dec(x_57);
x_58 = lean_ctor_get(x_9, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_9, 2);
lean_dec(x_59);
x_60 = lean_ctor_get(x_9, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_9, 0);
lean_dec(x_61);
lean_ctor_set(x_9, 4, x_16);
lean_ctor_set(x_9, 3, x_55);
lean_ctor_set(x_9, 2, x_14);
lean_ctor_set(x_9, 1, x_13);
lean_ctor_set(x_9, 0, x_53);
return x_9;
}
else
{
lean_object* x_62; 
lean_dec(x_9);
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_53);
lean_ctor_set(x_62, 1, x_13);
lean_ctor_set(x_62, 2, x_14);
lean_ctor_set(x_62, 3, x_55);
lean_ctor_set(x_62, 4, x_16);
return x_62;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_9, 0);
lean_inc(x_63);
x_64 = lean_nat_add(x_10, x_63);
lean_dec(x_63);
if (lean_is_scalar(x_7)) {
 x_65 = lean_alloc_ctor(0, 5, 0);
} else {
 x_65 = x_7;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_3);
lean_ctor_set(x_65, 2, x_4);
lean_ctor_set(x_65, 3, x_9);
lean_ctor_set(x_65, 4, x_6);
return x_65;
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_6, 3);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_6, 4);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_6);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_6, 0);
x_70 = lean_ctor_get(x_6, 1);
x_71 = lean_ctor_get(x_6, 2);
x_72 = lean_ctor_get(x_6, 4);
lean_dec(x_72);
x_73 = lean_ctor_get(x_6, 3);
lean_dec(x_73);
x_74 = lean_ctor_get(x_66, 0);
lean_inc(x_74);
x_75 = lean_nat_add(x_10, x_69);
lean_dec(x_69);
x_76 = lean_nat_add(x_10, x_74);
lean_dec(x_74);
lean_ctor_set(x_6, 4, x_66);
lean_ctor_set(x_6, 3, x_9);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_76);
if (lean_is_scalar(x_7)) {
 x_77 = lean_alloc_ctor(0, 5, 0);
} else {
 x_77 = x_7;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_70);
lean_ctor_set(x_77, 2, x_71);
lean_ctor_set(x_77, 3, x_6);
lean_ctor_set(x_77, 4, x_67);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_78 = lean_ctor_get(x_6, 0);
x_79 = lean_ctor_get(x_6, 1);
x_80 = lean_ctor_get(x_6, 2);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_6);
x_81 = lean_ctor_get(x_66, 0);
lean_inc(x_81);
x_82 = lean_nat_add(x_10, x_78);
lean_dec(x_78);
x_83 = lean_nat_add(x_10, x_81);
lean_dec(x_81);
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_3);
lean_ctor_set(x_84, 2, x_4);
lean_ctor_set(x_84, 3, x_9);
lean_ctor_set(x_84, 4, x_66);
if (lean_is_scalar(x_7)) {
 x_85 = lean_alloc_ctor(0, 5, 0);
} else {
 x_85 = x_7;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_79);
lean_ctor_set(x_85, 2, x_80);
lean_ctor_set(x_85, 3, x_84);
lean_ctor_set(x_85, 4, x_67);
return x_85;
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_6);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_6, 4);
lean_dec(x_87);
x_88 = lean_ctor_get(x_6, 3);
lean_dec(x_88);
x_89 = lean_ctor_get(x_6, 0);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_66);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = lean_ctor_get(x_66, 1);
x_92 = lean_ctor_get(x_66, 2);
x_93 = lean_ctor_get(x_66, 4);
lean_dec(x_93);
x_94 = lean_ctor_get(x_66, 3);
lean_dec(x_94);
x_95 = lean_ctor_get(x_66, 0);
lean_dec(x_95);
x_96 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_66, 4, x_67);
lean_ctor_set(x_66, 3, x_67);
lean_ctor_set(x_66, 2, x_4);
lean_ctor_set(x_66, 1, x_3);
lean_ctor_set(x_66, 0, x_10);
lean_ctor_set(x_6, 3, x_67);
lean_ctor_set(x_6, 0, x_10);
if (lean_is_scalar(x_7)) {
 x_97 = lean_alloc_ctor(0, 5, 0);
} else {
 x_97 = x_7;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_91);
lean_ctor_set(x_97, 2, x_92);
lean_ctor_set(x_97, 3, x_66);
lean_ctor_set(x_97, 4, x_6);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_66, 1);
x_99 = lean_ctor_get(x_66, 2);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_66);
x_100 = lean_unsigned_to_nat(3u);
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_10);
lean_ctor_set(x_101, 1, x_3);
lean_ctor_set(x_101, 2, x_4);
lean_ctor_set(x_101, 3, x_67);
lean_ctor_set(x_101, 4, x_67);
lean_ctor_set(x_6, 3, x_67);
lean_ctor_set(x_6, 0, x_10);
if (lean_is_scalar(x_7)) {
 x_102 = lean_alloc_ctor(0, 5, 0);
} else {
 x_102 = x_7;
}
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_98);
lean_ctor_set(x_102, 2, x_99);
lean_ctor_set(x_102, 3, x_101);
lean_ctor_set(x_102, 4, x_6);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_103 = lean_ctor_get(x_6, 1);
x_104 = lean_ctor_get(x_6, 2);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_6);
x_105 = lean_ctor_get(x_66, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_66, 2);
lean_inc(x_106);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 lean_ctor_release(x_66, 2);
 lean_ctor_release(x_66, 3);
 lean_ctor_release(x_66, 4);
 x_107 = x_66;
} else {
 lean_dec_ref(x_66);
 x_107 = lean_box(0);
}
x_108 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(0, 5, 0);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_10);
lean_ctor_set(x_109, 1, x_3);
lean_ctor_set(x_109, 2, x_4);
lean_ctor_set(x_109, 3, x_67);
lean_ctor_set(x_109, 4, x_67);
x_110 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_110, 0, x_10);
lean_ctor_set(x_110, 1, x_103);
lean_ctor_set(x_110, 2, x_104);
lean_ctor_set(x_110, 3, x_67);
lean_ctor_set(x_110, 4, x_67);
if (lean_is_scalar(x_7)) {
 x_111 = lean_alloc_ctor(0, 5, 0);
} else {
 x_111 = x_7;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_105);
lean_ctor_set(x_111, 2, x_106);
lean_ctor_set(x_111, 3, x_109);
lean_ctor_set(x_111, 4, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_6, 4);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_6);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = lean_ctor_get(x_6, 1);
x_115 = lean_ctor_get(x_6, 2);
x_116 = lean_ctor_get(x_6, 4);
lean_dec(x_116);
x_117 = lean_ctor_get(x_6, 3);
lean_dec(x_117);
x_118 = lean_ctor_get(x_6, 0);
lean_dec(x_118);
x_119 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_6, 4, x_66);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_10);
if (lean_is_scalar(x_7)) {
 x_120 = lean_alloc_ctor(0, 5, 0);
} else {
 x_120 = x_7;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_114);
lean_ctor_set(x_120, 2, x_115);
lean_ctor_set(x_120, 3, x_6);
lean_ctor_set(x_120, 4, x_112);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_6, 1);
x_122 = lean_ctor_get(x_6, 2);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_6);
x_123 = lean_unsigned_to_nat(3u);
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_10);
lean_ctor_set(x_124, 1, x_3);
lean_ctor_set(x_124, 2, x_4);
lean_ctor_set(x_124, 3, x_66);
lean_ctor_set(x_124, 4, x_66);
if (lean_is_scalar(x_7)) {
 x_125 = lean_alloc_ctor(0, 5, 0);
} else {
 x_125 = x_7;
}
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_121);
lean_ctor_set(x_125, 2, x_122);
lean_ctor_set(x_125, 3, x_124);
lean_ctor_set(x_125, 4, x_112);
return x_125;
}
}
else
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_6);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_6, 4);
lean_dec(x_127);
x_128 = lean_ctor_get(x_6, 3);
lean_dec(x_128);
lean_ctor_set(x_6, 3, x_112);
x_129 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_7)) {
 x_130 = lean_alloc_ctor(0, 5, 0);
} else {
 x_130 = x_7;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_3);
lean_ctor_set(x_130, 2, x_4);
lean_ctor_set(x_130, 3, x_112);
lean_ctor_set(x_130, 4, x_6);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = lean_ctor_get(x_6, 0);
x_132 = lean_ctor_get(x_6, 1);
x_133 = lean_ctor_get(x_6, 2);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_6);
x_134 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
lean_ctor_set(x_134, 2, x_133);
lean_ctor_set(x_134, 3, x_112);
lean_ctor_set(x_134, 4, x_112);
x_135 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_7)) {
 x_136 = lean_alloc_ctor(0, 5, 0);
} else {
 x_136 = x_7;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_3);
lean_ctor_set(x_136, 2, x_4);
lean_ctor_set(x_136, 3, x_112);
lean_ctor_set(x_136, 4, x_134);
return x_136;
}
}
}
}
else
{
lean_object* x_137; 
if (lean_is_scalar(x_7)) {
 x_137 = lean_alloc_ctor(0, 5, 0);
} else {
 x_137 = x_7;
}
lean_ctor_set(x_137, 0, x_10);
lean_ctor_set(x_137, 1, x_3);
lean_ctor_set(x_137, 2, x_4);
lean_ctor_set(x_137, 3, x_6);
lean_ctor_set(x_137, 4, x_6);
return x_137;
}
}
}
case 1:
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_138 = lean_ctor_get(x_5, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_5, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_5, 2);
lean_inc(x_140);
x_141 = lean_ctor_get(x_5, 3);
lean_inc(x_141);
x_142 = lean_ctor_get(x_5, 4);
lean_inc(x_142);
x_143 = lean_ctor_get(x_6, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_6, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_6, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_6, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_6, 4);
lean_inc(x_147);
x_148 = lean_unsigned_to_nat(1u);
x_149 = lean_nat_dec_lt(x_138, x_143);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_138);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 x_150 = x_5;
} else {
 lean_dec_ref(x_5);
 x_150 = lean_box(0);
}
x_151 = l_Std_DTreeMap_Internal_Impl_maxView___redArg(x_139, x_140, x_141, x_142);
x_152 = lean_ctor_get(x_151, 2);
lean_inc(x_152);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec_ref(x_151);
x_155 = lean_ctor_get(x_152, 0);
lean_inc(x_155);
x_156 = lean_unsigned_to_nat(3u);
x_157 = lean_nat_mul(x_156, x_155);
x_158 = lean_nat_dec_lt(x_157, x_143);
lean_dec(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
x_159 = lean_nat_add(x_148, x_155);
lean_dec(x_155);
x_160 = lean_nat_add(x_159, x_143);
lean_dec(x_143);
lean_dec(x_159);
if (lean_is_scalar(x_150)) {
 x_161 = lean_alloc_ctor(0, 5, 0);
} else {
 x_161 = x_150;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_153);
lean_ctor_set(x_161, 2, x_154);
lean_ctor_set(x_161, 3, x_152);
lean_ctor_set(x_161, 4, x_6);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_162 = x_6;
} else {
 lean_dec_ref(x_6);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_146, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_146, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_146, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_146, 3);
lean_inc(x_166);
x_167 = lean_ctor_get(x_146, 4);
lean_inc(x_167);
x_168 = lean_ctor_get(x_147, 0);
lean_inc(x_168);
x_169 = lean_unsigned_to_nat(2u);
x_170 = lean_nat_mul(x_169, x_168);
x_171 = lean_nat_dec_lt(x_163, x_170);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_182; 
lean_dec(x_163);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 lean_ctor_release(x_146, 2);
 lean_ctor_release(x_146, 3);
 lean_ctor_release(x_146, 4);
 x_172 = x_146;
} else {
 lean_dec_ref(x_146);
 x_172 = lean_box(0);
}
x_173 = lean_nat_add(x_148, x_155);
lean_dec(x_155);
x_174 = lean_nat_add(x_173, x_143);
lean_dec(x_143);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_166, 0);
lean_inc(x_189);
x_182 = x_189;
goto block_188;
}
else
{
lean_object* x_190; 
x_190 = lean_unsigned_to_nat(0u);
x_182 = x_190;
goto block_188;
}
block_181:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_nat_add(x_175, x_177);
lean_dec(x_177);
lean_dec(x_175);
if (lean_is_scalar(x_172)) {
 x_179 = lean_alloc_ctor(0, 5, 0);
} else {
 x_179 = x_172;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_144);
lean_ctor_set(x_179, 2, x_145);
lean_ctor_set(x_179, 3, x_167);
lean_ctor_set(x_179, 4, x_147);
if (lean_is_scalar(x_162)) {
 x_180 = lean_alloc_ctor(0, 5, 0);
} else {
 x_180 = x_162;
}
lean_ctor_set(x_180, 0, x_174);
lean_ctor_set(x_180, 1, x_164);
lean_ctor_set(x_180, 2, x_165);
lean_ctor_set(x_180, 3, x_176);
lean_ctor_set(x_180, 4, x_179);
return x_180;
}
block_188:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_nat_add(x_173, x_182);
lean_dec(x_182);
lean_dec(x_173);
if (lean_is_scalar(x_150)) {
 x_184 = lean_alloc_ctor(0, 5, 0);
} else {
 x_184 = x_150;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_153);
lean_ctor_set(x_184, 2, x_154);
lean_ctor_set(x_184, 3, x_152);
lean_ctor_set(x_184, 4, x_166);
x_185 = lean_nat_add(x_148, x_168);
lean_dec(x_168);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_167, 0);
lean_inc(x_186);
x_175 = x_185;
x_176 = x_184;
x_177 = x_186;
goto block_181;
}
else
{
lean_object* x_187; 
x_187 = lean_unsigned_to_nat(0u);
x_175 = x_185;
x_176 = x_184;
x_177 = x_187;
goto block_181;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
x_191 = lean_nat_add(x_148, x_155);
lean_dec(x_155);
x_192 = lean_nat_add(x_191, x_143);
lean_dec(x_143);
x_193 = lean_nat_add(x_191, x_163);
lean_dec(x_163);
lean_dec(x_191);
if (lean_is_scalar(x_162)) {
 x_194 = lean_alloc_ctor(0, 5, 0);
} else {
 x_194 = x_162;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_153);
lean_ctor_set(x_194, 2, x_154);
lean_ctor_set(x_194, 3, x_152);
lean_ctor_set(x_194, 4, x_146);
if (lean_is_scalar(x_150)) {
 x_195 = lean_alloc_ctor(0, 5, 0);
} else {
 x_195 = x_150;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_144);
lean_ctor_set(x_195, 2, x_145);
lean_ctor_set(x_195, 3, x_194);
lean_ctor_set(x_195, 4, x_147);
return x_195;
}
}
}
else
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_6);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_6, 4);
lean_dec(x_197);
x_198 = lean_ctor_get(x_6, 3);
lean_dec(x_198);
x_199 = lean_ctor_get(x_6, 2);
lean_dec(x_199);
x_200 = lean_ctor_get(x_6, 1);
lean_dec(x_200);
x_201 = lean_ctor_get(x_6, 0);
lean_dec(x_201);
if (lean_obj_tag(x_146) == 0)
{
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_202 = lean_ctor_get(x_151, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_151, 1);
lean_inc(x_203);
lean_dec_ref(x_151);
x_204 = lean_ctor_get(x_146, 0);
lean_inc(x_204);
x_205 = lean_nat_add(x_148, x_143);
lean_dec(x_143);
x_206 = lean_nat_add(x_148, x_204);
lean_dec(x_204);
lean_ctor_set(x_6, 4, x_146);
lean_ctor_set(x_6, 3, x_152);
lean_ctor_set(x_6, 2, x_203);
lean_ctor_set(x_6, 1, x_202);
lean_ctor_set(x_6, 0, x_206);
if (lean_is_scalar(x_150)) {
 x_207 = lean_alloc_ctor(0, 5, 0);
} else {
 x_207 = x_150;
}
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_144);
lean_ctor_set(x_207, 2, x_145);
lean_ctor_set(x_207, 3, x_6);
lean_ctor_set(x_207, 4, x_147);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
lean_dec(x_143);
x_208 = lean_ctor_get(x_151, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_151, 1);
lean_inc(x_209);
lean_dec_ref(x_151);
x_210 = !lean_is_exclusive(x_146);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_211 = lean_ctor_get(x_146, 1);
x_212 = lean_ctor_get(x_146, 2);
x_213 = lean_ctor_get(x_146, 4);
lean_dec(x_213);
x_214 = lean_ctor_get(x_146, 3);
lean_dec(x_214);
x_215 = lean_ctor_get(x_146, 0);
lean_dec(x_215);
x_216 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_146, 4, x_147);
lean_ctor_set(x_146, 3, x_147);
lean_ctor_set(x_146, 2, x_209);
lean_ctor_set(x_146, 1, x_208);
lean_ctor_set(x_146, 0, x_148);
lean_ctor_set(x_6, 3, x_147);
lean_ctor_set(x_6, 0, x_148);
if (lean_is_scalar(x_150)) {
 x_217 = lean_alloc_ctor(0, 5, 0);
} else {
 x_217 = x_150;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_211);
lean_ctor_set(x_217, 2, x_212);
lean_ctor_set(x_217, 3, x_146);
lean_ctor_set(x_217, 4, x_6);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_218 = lean_ctor_get(x_146, 1);
x_219 = lean_ctor_get(x_146, 2);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_146);
x_220 = lean_unsigned_to_nat(3u);
x_221 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_221, 0, x_148);
lean_ctor_set(x_221, 1, x_208);
lean_ctor_set(x_221, 2, x_209);
lean_ctor_set(x_221, 3, x_147);
lean_ctor_set(x_221, 4, x_147);
lean_ctor_set(x_6, 3, x_147);
lean_ctor_set(x_6, 0, x_148);
if (lean_is_scalar(x_150)) {
 x_222 = lean_alloc_ctor(0, 5, 0);
} else {
 x_222 = x_150;
}
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_218);
lean_ctor_set(x_222, 2, x_219);
lean_ctor_set(x_222, 3, x_221);
lean_ctor_set(x_222, 4, x_6);
return x_222;
}
}
}
else
{
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_143);
x_223 = lean_ctor_get(x_151, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_151, 1);
lean_inc(x_224);
lean_dec_ref(x_151);
x_225 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_6, 4, x_146);
lean_ctor_set(x_6, 2, x_224);
lean_ctor_set(x_6, 1, x_223);
lean_ctor_set(x_6, 0, x_148);
if (lean_is_scalar(x_150)) {
 x_226 = lean_alloc_ctor(0, 5, 0);
} else {
 x_226 = x_150;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_144);
lean_ctor_set(x_226, 2, x_145);
lean_ctor_set(x_226, 3, x_6);
lean_ctor_set(x_226, 4, x_147);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_227 = lean_ctor_get(x_151, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_151, 1);
lean_inc(x_228);
lean_dec_ref(x_151);
lean_ctor_set(x_6, 3, x_147);
x_229 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_150)) {
 x_230 = lean_alloc_ctor(0, 5, 0);
} else {
 x_230 = x_150;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_227);
lean_ctor_set(x_230, 2, x_228);
lean_ctor_set(x_230, 3, x_147);
lean_ctor_set(x_230, 4, x_6);
return x_230;
}
}
}
else
{
lean_dec(x_6);
if (lean_obj_tag(x_146) == 0)
{
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_231 = lean_ctor_get(x_151, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_151, 1);
lean_inc(x_232);
lean_dec_ref(x_151);
x_233 = lean_ctor_get(x_146, 0);
lean_inc(x_233);
x_234 = lean_nat_add(x_148, x_143);
lean_dec(x_143);
x_235 = lean_nat_add(x_148, x_233);
lean_dec(x_233);
x_236 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_231);
lean_ctor_set(x_236, 2, x_232);
lean_ctor_set(x_236, 3, x_152);
lean_ctor_set(x_236, 4, x_146);
if (lean_is_scalar(x_150)) {
 x_237 = lean_alloc_ctor(0, 5, 0);
} else {
 x_237 = x_150;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_144);
lean_ctor_set(x_237, 2, x_145);
lean_ctor_set(x_237, 3, x_236);
lean_ctor_set(x_237, 4, x_147);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_143);
x_238 = lean_ctor_get(x_151, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_151, 1);
lean_inc(x_239);
lean_dec_ref(x_151);
x_240 = lean_ctor_get(x_146, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_146, 2);
lean_inc(x_241);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 lean_ctor_release(x_146, 2);
 lean_ctor_release(x_146, 3);
 lean_ctor_release(x_146, 4);
 x_242 = x_146;
} else {
 lean_dec_ref(x_146);
 x_242 = lean_box(0);
}
x_243 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_242)) {
 x_244 = lean_alloc_ctor(0, 5, 0);
} else {
 x_244 = x_242;
}
lean_ctor_set(x_244, 0, x_148);
lean_ctor_set(x_244, 1, x_238);
lean_ctor_set(x_244, 2, x_239);
lean_ctor_set(x_244, 3, x_147);
lean_ctor_set(x_244, 4, x_147);
x_245 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_245, 0, x_148);
lean_ctor_set(x_245, 1, x_144);
lean_ctor_set(x_245, 2, x_145);
lean_ctor_set(x_245, 3, x_147);
lean_ctor_set(x_245, 4, x_147);
if (lean_is_scalar(x_150)) {
 x_246 = lean_alloc_ctor(0, 5, 0);
} else {
 x_246 = x_150;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_240);
lean_ctor_set(x_246, 2, x_241);
lean_ctor_set(x_246, 3, x_244);
lean_ctor_set(x_246, 4, x_245);
return x_246;
}
}
else
{
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_143);
x_247 = lean_ctor_get(x_151, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_151, 1);
lean_inc(x_248);
lean_dec_ref(x_151);
x_249 = lean_unsigned_to_nat(3u);
x_250 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_250, 0, x_148);
lean_ctor_set(x_250, 1, x_247);
lean_ctor_set(x_250, 2, x_248);
lean_ctor_set(x_250, 3, x_146);
lean_ctor_set(x_250, 4, x_146);
if (lean_is_scalar(x_150)) {
 x_251 = lean_alloc_ctor(0, 5, 0);
} else {
 x_251 = x_150;
}
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_144);
lean_ctor_set(x_251, 2, x_145);
lean_ctor_set(x_251, 3, x_250);
lean_ctor_set(x_251, 4, x_147);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = lean_ctor_get(x_151, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_151, 1);
lean_inc(x_253);
lean_dec_ref(x_151);
x_254 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_254, 0, x_143);
lean_ctor_set(x_254, 1, x_144);
lean_ctor_set(x_254, 2, x_145);
lean_ctor_set(x_254, 3, x_147);
lean_ctor_set(x_254, 4, x_147);
x_255 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_150)) {
 x_256 = lean_alloc_ctor(0, 5, 0);
} else {
 x_256 = x_150;
}
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_252);
lean_ctor_set(x_256, 2, x_253);
lean_ctor_set(x_256, 3, x_147);
lean_ctor_set(x_256, 4, x_254);
return x_256;
}
}
}
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_143);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_257 = x_6;
} else {
 lean_dec_ref(x_6);
 x_257 = lean_box(0);
}
x_258 = l_Std_DTreeMap_Internal_Impl_minView___redArg(x_144, x_145, x_146, x_147);
x_259 = lean_ctor_get(x_258, 2);
lean_inc(x_259);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_260 = lean_ctor_get(x_258, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_261);
lean_dec_ref(x_258);
x_262 = lean_ctor_get(x_259, 0);
lean_inc(x_262);
x_263 = lean_unsigned_to_nat(3u);
x_264 = lean_nat_mul(x_263, x_262);
x_265 = lean_nat_dec_lt(x_264, x_138);
lean_dec(x_264);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
x_266 = lean_nat_add(x_148, x_138);
lean_dec(x_138);
x_267 = lean_nat_add(x_266, x_262);
lean_dec(x_262);
lean_dec(x_266);
if (lean_is_scalar(x_257)) {
 x_268 = lean_alloc_ctor(0, 5, 0);
} else {
 x_268 = x_257;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_260);
lean_ctor_set(x_268, 2, x_261);
lean_ctor_set(x_268, 3, x_5);
lean_ctor_set(x_268, 4, x_259);
return x_268;
}
else
{
uint8_t x_269; 
x_269 = !lean_is_exclusive(x_5);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_270 = lean_ctor_get(x_5, 4);
lean_dec(x_270);
x_271 = lean_ctor_get(x_5, 3);
lean_dec(x_271);
x_272 = lean_ctor_get(x_5, 2);
lean_dec(x_272);
x_273 = lean_ctor_get(x_5, 1);
lean_dec(x_273);
x_274 = lean_ctor_get(x_5, 0);
lean_dec(x_274);
x_275 = lean_ctor_get(x_141, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_142, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_142, 1);
lean_inc(x_277);
x_278 = lean_ctor_get(x_142, 2);
lean_inc(x_278);
x_279 = lean_ctor_get(x_142, 3);
lean_inc(x_279);
x_280 = lean_ctor_get(x_142, 4);
lean_inc(x_280);
x_281 = lean_unsigned_to_nat(2u);
x_282 = lean_nat_mul(x_281, x_275);
x_283 = lean_nat_dec_lt(x_276, x_282);
lean_dec(x_282);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_300; lean_object* x_301; 
lean_dec(x_276);
lean_free_object(x_5);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 lean_ctor_release(x_142, 4);
 x_284 = x_142;
} else {
 lean_dec_ref(x_142);
 x_284 = lean_box(0);
}
x_285 = lean_nat_add(x_148, x_138);
lean_dec(x_138);
x_286 = lean_nat_add(x_285, x_262);
lean_dec(x_285);
x_300 = lean_nat_add(x_148, x_275);
lean_dec(x_275);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_308; 
x_308 = lean_ctor_get(x_279, 0);
lean_inc(x_308);
x_301 = x_308;
goto block_307;
}
else
{
lean_object* x_309; 
x_309 = lean_unsigned_to_nat(0u);
x_301 = x_309;
goto block_307;
}
block_299:
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_290 = lean_nat_add(x_287, x_289);
lean_dec(x_289);
lean_dec(x_287);
lean_inc_ref(x_259);
if (lean_is_scalar(x_284)) {
 x_291 = lean_alloc_ctor(0, 5, 0);
} else {
 x_291 = x_284;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_260);
lean_ctor_set(x_291, 2, x_261);
lean_ctor_set(x_291, 3, x_280);
lean_ctor_set(x_291, 4, x_259);
x_292 = !lean_is_exclusive(x_259);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_ctor_get(x_259, 4);
lean_dec(x_293);
x_294 = lean_ctor_get(x_259, 3);
lean_dec(x_294);
x_295 = lean_ctor_get(x_259, 2);
lean_dec(x_295);
x_296 = lean_ctor_get(x_259, 1);
lean_dec(x_296);
x_297 = lean_ctor_get(x_259, 0);
lean_dec(x_297);
lean_ctor_set(x_259, 4, x_291);
lean_ctor_set(x_259, 3, x_288);
lean_ctor_set(x_259, 2, x_278);
lean_ctor_set(x_259, 1, x_277);
lean_ctor_set(x_259, 0, x_286);
return x_259;
}
else
{
lean_object* x_298; 
lean_dec(x_259);
x_298 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_298, 0, x_286);
lean_ctor_set(x_298, 1, x_277);
lean_ctor_set(x_298, 2, x_278);
lean_ctor_set(x_298, 3, x_288);
lean_ctor_set(x_298, 4, x_291);
return x_298;
}
}
block_307:
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_nat_add(x_300, x_301);
lean_dec(x_301);
lean_dec(x_300);
if (lean_is_scalar(x_257)) {
 x_303 = lean_alloc_ctor(0, 5, 0);
} else {
 x_303 = x_257;
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_139);
lean_ctor_set(x_303, 2, x_140);
lean_ctor_set(x_303, 3, x_141);
lean_ctor_set(x_303, 4, x_279);
x_304 = lean_nat_add(x_148, x_262);
lean_dec(x_262);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_305; 
x_305 = lean_ctor_get(x_280, 0);
lean_inc(x_305);
x_287 = x_304;
x_288 = x_303;
x_289 = x_305;
goto block_299;
}
else
{
lean_object* x_306; 
x_306 = lean_unsigned_to_nat(0u);
x_287 = x_304;
x_288 = x_303;
x_289 = x_306;
goto block_299;
}
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_280);
lean_dec(x_279);
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_275);
x_310 = lean_nat_add(x_148, x_138);
lean_dec(x_138);
x_311 = lean_nat_add(x_310, x_262);
lean_dec(x_310);
x_312 = lean_nat_add(x_148, x_262);
lean_dec(x_262);
x_313 = lean_nat_add(x_312, x_276);
lean_dec(x_276);
lean_dec(x_312);
if (lean_is_scalar(x_257)) {
 x_314 = lean_alloc_ctor(0, 5, 0);
} else {
 x_314 = x_257;
}
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_260);
lean_ctor_set(x_314, 2, x_261);
lean_ctor_set(x_314, 3, x_142);
lean_ctor_set(x_314, 4, x_259);
lean_ctor_set(x_5, 4, x_314);
lean_ctor_set(x_5, 0, x_311);
return x_5;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; 
lean_dec(x_5);
x_315 = lean_ctor_get(x_141, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_142, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_142, 1);
lean_inc(x_317);
x_318 = lean_ctor_get(x_142, 2);
lean_inc(x_318);
x_319 = lean_ctor_get(x_142, 3);
lean_inc(x_319);
x_320 = lean_ctor_get(x_142, 4);
lean_inc(x_320);
x_321 = lean_unsigned_to_nat(2u);
x_322 = lean_nat_mul(x_321, x_315);
x_323 = lean_nat_dec_lt(x_316, x_322);
lean_dec(x_322);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_335; lean_object* x_336; 
lean_dec(x_316);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 lean_ctor_release(x_142, 4);
 x_324 = x_142;
} else {
 lean_dec_ref(x_142);
 x_324 = lean_box(0);
}
x_325 = lean_nat_add(x_148, x_138);
lean_dec(x_138);
x_326 = lean_nat_add(x_325, x_262);
lean_dec(x_325);
x_335 = lean_nat_add(x_148, x_315);
lean_dec(x_315);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_343; 
x_343 = lean_ctor_get(x_319, 0);
lean_inc(x_343);
x_336 = x_343;
goto block_342;
}
else
{
lean_object* x_344; 
x_344 = lean_unsigned_to_nat(0u);
x_336 = x_344;
goto block_342;
}
block_334:
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_330 = lean_nat_add(x_327, x_329);
lean_dec(x_329);
lean_dec(x_327);
lean_inc_ref(x_259);
if (lean_is_scalar(x_324)) {
 x_331 = lean_alloc_ctor(0, 5, 0);
} else {
 x_331 = x_324;
}
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_260);
lean_ctor_set(x_331, 2, x_261);
lean_ctor_set(x_331, 3, x_320);
lean_ctor_set(x_331, 4, x_259);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 lean_ctor_release(x_259, 2);
 lean_ctor_release(x_259, 3);
 lean_ctor_release(x_259, 4);
 x_332 = x_259;
} else {
 lean_dec_ref(x_259);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(0, 5, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_326);
lean_ctor_set(x_333, 1, x_317);
lean_ctor_set(x_333, 2, x_318);
lean_ctor_set(x_333, 3, x_328);
lean_ctor_set(x_333, 4, x_331);
return x_333;
}
block_342:
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_nat_add(x_335, x_336);
lean_dec(x_336);
lean_dec(x_335);
if (lean_is_scalar(x_257)) {
 x_338 = lean_alloc_ctor(0, 5, 0);
} else {
 x_338 = x_257;
}
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_139);
lean_ctor_set(x_338, 2, x_140);
lean_ctor_set(x_338, 3, x_141);
lean_ctor_set(x_338, 4, x_319);
x_339 = lean_nat_add(x_148, x_262);
lean_dec(x_262);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_340; 
x_340 = lean_ctor_get(x_320, 0);
lean_inc(x_340);
x_327 = x_339;
x_328 = x_338;
x_329 = x_340;
goto block_334;
}
else
{
lean_object* x_341; 
x_341 = lean_unsigned_to_nat(0u);
x_327 = x_339;
x_328 = x_338;
x_329 = x_341;
goto block_334;
}
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_315);
x_345 = lean_nat_add(x_148, x_138);
lean_dec(x_138);
x_346 = lean_nat_add(x_345, x_262);
lean_dec(x_345);
x_347 = lean_nat_add(x_148, x_262);
lean_dec(x_262);
x_348 = lean_nat_add(x_347, x_316);
lean_dec(x_316);
lean_dec(x_347);
if (lean_is_scalar(x_257)) {
 x_349 = lean_alloc_ctor(0, 5, 0);
} else {
 x_349 = x_257;
}
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_260);
lean_ctor_set(x_349, 2, x_261);
lean_ctor_set(x_349, 3, x_142);
lean_ctor_set(x_349, 4, x_259);
x_350 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_350, 0, x_346);
lean_ctor_set(x_350, 1, x_139);
lean_ctor_set(x_350, 2, x_140);
lean_ctor_set(x_350, 3, x_141);
lean_ctor_set(x_350, 4, x_349);
return x_350;
}
}
}
}
else
{
if (lean_obj_tag(x_141) == 0)
{
uint8_t x_351; 
x_351 = !lean_is_exclusive(x_5);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_352 = lean_ctor_get(x_5, 4);
lean_dec(x_352);
x_353 = lean_ctor_get(x_5, 3);
lean_dec(x_353);
x_354 = lean_ctor_get(x_5, 2);
lean_dec(x_354);
x_355 = lean_ctor_get(x_5, 1);
lean_dec(x_355);
x_356 = lean_ctor_get(x_5, 0);
lean_dec(x_356);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_357 = lean_ctor_get(x_258, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_258, 1);
lean_inc(x_358);
lean_dec_ref(x_258);
x_359 = lean_ctor_get(x_142, 0);
lean_inc(x_359);
x_360 = lean_nat_add(x_148, x_138);
lean_dec(x_138);
x_361 = lean_nat_add(x_148, x_359);
lean_dec(x_359);
if (lean_is_scalar(x_257)) {
 x_362 = lean_alloc_ctor(0, 5, 0);
} else {
 x_362 = x_257;
}
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_357);
lean_ctor_set(x_362, 2, x_358);
lean_ctor_set(x_362, 3, x_142);
lean_ctor_set(x_362, 4, x_259);
lean_ctor_set(x_5, 4, x_362);
lean_ctor_set(x_5, 0, x_360);
return x_5;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_138);
x_363 = lean_ctor_get(x_258, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_258, 1);
lean_inc(x_364);
lean_dec_ref(x_258);
x_365 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_257)) {
 x_366 = lean_alloc_ctor(0, 5, 0);
} else {
 x_366 = x_257;
}
lean_ctor_set(x_366, 0, x_148);
lean_ctor_set(x_366, 1, x_363);
lean_ctor_set(x_366, 2, x_364);
lean_ctor_set(x_366, 3, x_142);
lean_ctor_set(x_366, 4, x_142);
lean_ctor_set(x_5, 4, x_366);
lean_ctor_set(x_5, 0, x_365);
return x_5;
}
}
else
{
lean_dec(x_5);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_367 = lean_ctor_get(x_258, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_258, 1);
lean_inc(x_368);
lean_dec_ref(x_258);
x_369 = lean_ctor_get(x_142, 0);
lean_inc(x_369);
x_370 = lean_nat_add(x_148, x_138);
lean_dec(x_138);
x_371 = lean_nat_add(x_148, x_369);
lean_dec(x_369);
if (lean_is_scalar(x_257)) {
 x_372 = lean_alloc_ctor(0, 5, 0);
} else {
 x_372 = x_257;
}
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_367);
lean_ctor_set(x_372, 2, x_368);
lean_ctor_set(x_372, 3, x_142);
lean_ctor_set(x_372, 4, x_259);
x_373 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_373, 0, x_370);
lean_ctor_set(x_373, 1, x_139);
lean_ctor_set(x_373, 2, x_140);
lean_ctor_set(x_373, 3, x_141);
lean_ctor_set(x_373, 4, x_372);
return x_373;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_138);
x_374 = lean_ctor_get(x_258, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_258, 1);
lean_inc(x_375);
lean_dec_ref(x_258);
x_376 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_257)) {
 x_377 = lean_alloc_ctor(0, 5, 0);
} else {
 x_377 = x_257;
}
lean_ctor_set(x_377, 0, x_148);
lean_ctor_set(x_377, 1, x_374);
lean_ctor_set(x_377, 2, x_375);
lean_ctor_set(x_377, 3, x_142);
lean_ctor_set(x_377, 4, x_142);
x_378 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_139);
lean_ctor_set(x_378, 2, x_140);
lean_ctor_set(x_378, 3, x_141);
lean_ctor_set(x_378, 4, x_377);
return x_378;
}
}
}
else
{
lean_dec(x_138);
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_379; 
x_379 = !lean_is_exclusive(x_5);
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; 
x_380 = lean_ctor_get(x_5, 4);
lean_dec(x_380);
x_381 = lean_ctor_get(x_5, 3);
lean_dec(x_381);
x_382 = lean_ctor_get(x_5, 2);
lean_dec(x_382);
x_383 = lean_ctor_get(x_5, 1);
lean_dec(x_383);
x_384 = lean_ctor_get(x_5, 0);
lean_dec(x_384);
x_385 = lean_ctor_get(x_258, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_258, 1);
lean_inc(x_386);
lean_dec_ref(x_258);
x_387 = !lean_is_exclusive(x_142);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_388 = lean_ctor_get(x_142, 1);
x_389 = lean_ctor_get(x_142, 2);
x_390 = lean_ctor_get(x_142, 4);
lean_dec(x_390);
x_391 = lean_ctor_get(x_142, 3);
lean_dec(x_391);
x_392 = lean_ctor_get(x_142, 0);
lean_dec(x_392);
x_393 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_142, 4, x_141);
lean_ctor_set(x_142, 3, x_141);
lean_ctor_set(x_142, 2, x_140);
lean_ctor_set(x_142, 1, x_139);
lean_ctor_set(x_142, 0, x_148);
if (lean_is_scalar(x_257)) {
 x_394 = lean_alloc_ctor(0, 5, 0);
} else {
 x_394 = x_257;
}
lean_ctor_set(x_394, 0, x_148);
lean_ctor_set(x_394, 1, x_385);
lean_ctor_set(x_394, 2, x_386);
lean_ctor_set(x_394, 3, x_141);
lean_ctor_set(x_394, 4, x_141);
lean_ctor_set(x_5, 4, x_394);
lean_ctor_set(x_5, 3, x_142);
lean_ctor_set(x_5, 2, x_389);
lean_ctor_set(x_5, 1, x_388);
lean_ctor_set(x_5, 0, x_393);
return x_5;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_395 = lean_ctor_get(x_142, 1);
x_396 = lean_ctor_get(x_142, 2);
lean_inc(x_396);
lean_inc(x_395);
lean_dec(x_142);
x_397 = lean_unsigned_to_nat(3u);
x_398 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_398, 0, x_148);
lean_ctor_set(x_398, 1, x_139);
lean_ctor_set(x_398, 2, x_140);
lean_ctor_set(x_398, 3, x_141);
lean_ctor_set(x_398, 4, x_141);
if (lean_is_scalar(x_257)) {
 x_399 = lean_alloc_ctor(0, 5, 0);
} else {
 x_399 = x_257;
}
lean_ctor_set(x_399, 0, x_148);
lean_ctor_set(x_399, 1, x_385);
lean_ctor_set(x_399, 2, x_386);
lean_ctor_set(x_399, 3, x_141);
lean_ctor_set(x_399, 4, x_141);
lean_ctor_set(x_5, 4, x_399);
lean_ctor_set(x_5, 3, x_398);
lean_ctor_set(x_5, 2, x_396);
lean_ctor_set(x_5, 1, x_395);
lean_ctor_set(x_5, 0, x_397);
return x_5;
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec(x_5);
x_400 = lean_ctor_get(x_258, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_258, 1);
lean_inc(x_401);
lean_dec_ref(x_258);
x_402 = lean_ctor_get(x_142, 1);
lean_inc(x_402);
x_403 = lean_ctor_get(x_142, 2);
lean_inc(x_403);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 lean_ctor_release(x_142, 4);
 x_404 = x_142;
} else {
 lean_dec_ref(x_142);
 x_404 = lean_box(0);
}
x_405 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_404)) {
 x_406 = lean_alloc_ctor(0, 5, 0);
} else {
 x_406 = x_404;
}
lean_ctor_set(x_406, 0, x_148);
lean_ctor_set(x_406, 1, x_139);
lean_ctor_set(x_406, 2, x_140);
lean_ctor_set(x_406, 3, x_141);
lean_ctor_set(x_406, 4, x_141);
if (lean_is_scalar(x_257)) {
 x_407 = lean_alloc_ctor(0, 5, 0);
} else {
 x_407 = x_257;
}
lean_ctor_set(x_407, 0, x_148);
lean_ctor_set(x_407, 1, x_400);
lean_ctor_set(x_407, 2, x_401);
lean_ctor_set(x_407, 3, x_141);
lean_ctor_set(x_407, 4, x_141);
x_408 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_408, 0, x_405);
lean_ctor_set(x_408, 1, x_402);
lean_ctor_set(x_408, 2, x_403);
lean_ctor_set(x_408, 3, x_406);
lean_ctor_set(x_408, 4, x_407);
return x_408;
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_140);
lean_dec(x_139);
x_409 = lean_ctor_get(x_258, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_258, 1);
lean_inc(x_410);
lean_dec_ref(x_258);
x_411 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_257)) {
 x_412 = lean_alloc_ctor(0, 5, 0);
} else {
 x_412 = x_257;
}
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_409);
lean_ctor_set(x_412, 2, x_410);
lean_ctor_set(x_412, 3, x_5);
lean_ctor_set(x_412, 4, x_142);
return x_412;
}
}
}
}
}
else
{
return x_5;
}
}
else
{
return x_6;
}
}
default: 
{
lean_object* x_413; lean_object* x_414; 
x_413 = l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_1, x_6);
x_414 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_413) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; 
x_415 = lean_ctor_get(x_413, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_5, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_5, 1);
lean_inc(x_417);
x_418 = lean_ctor_get(x_5, 2);
lean_inc(x_418);
x_419 = lean_ctor_get(x_5, 3);
lean_inc(x_419);
x_420 = lean_ctor_get(x_5, 4);
lean_inc(x_420);
x_421 = lean_unsigned_to_nat(3u);
x_422 = lean_nat_mul(x_421, x_415);
x_423 = lean_nat_dec_lt(x_422, x_416);
lean_dec(x_422);
if (x_423 == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_417);
x_424 = lean_nat_add(x_414, x_416);
lean_dec(x_416);
x_425 = lean_nat_add(x_424, x_415);
lean_dec(x_415);
lean_dec(x_424);
if (lean_is_scalar(x_7)) {
 x_426 = lean_alloc_ctor(0, 5, 0);
} else {
 x_426 = x_7;
}
lean_ctor_set(x_426, 0, x_425);
lean_ctor_set(x_426, 1, x_3);
lean_ctor_set(x_426, 2, x_4);
lean_ctor_set(x_426, 3, x_5);
lean_ctor_set(x_426, 4, x_413);
return x_426;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; uint8_t x_436; 
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 x_427 = x_5;
} else {
 lean_dec_ref(x_5);
 x_427 = lean_box(0);
}
x_428 = lean_ctor_get(x_419, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_420, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_420, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_420, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_420, 3);
lean_inc(x_432);
x_433 = lean_ctor_get(x_420, 4);
lean_inc(x_433);
x_434 = lean_unsigned_to_nat(2u);
x_435 = lean_nat_mul(x_434, x_428);
x_436 = lean_nat_dec_lt(x_429, x_435);
lean_dec(x_435);
if (x_436 == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_447; lean_object* x_448; 
lean_dec(x_429);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 lean_ctor_release(x_420, 4);
 x_437 = x_420;
} else {
 lean_dec_ref(x_420);
 x_437 = lean_box(0);
}
x_438 = lean_nat_add(x_414, x_416);
lean_dec(x_416);
x_439 = lean_nat_add(x_438, x_415);
lean_dec(x_438);
x_447 = lean_nat_add(x_414, x_428);
lean_dec(x_428);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_455; 
x_455 = lean_ctor_get(x_432, 0);
lean_inc(x_455);
x_448 = x_455;
goto block_454;
}
else
{
lean_object* x_456; 
x_456 = lean_unsigned_to_nat(0u);
x_448 = x_456;
goto block_454;
}
block_446:
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_nat_add(x_441, x_442);
lean_dec(x_442);
lean_dec(x_441);
if (lean_is_scalar(x_437)) {
 x_444 = lean_alloc_ctor(0, 5, 0);
} else {
 x_444 = x_437;
}
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_3);
lean_ctor_set(x_444, 2, x_4);
lean_ctor_set(x_444, 3, x_433);
lean_ctor_set(x_444, 4, x_413);
if (lean_is_scalar(x_427)) {
 x_445 = lean_alloc_ctor(0, 5, 0);
} else {
 x_445 = x_427;
}
lean_ctor_set(x_445, 0, x_439);
lean_ctor_set(x_445, 1, x_430);
lean_ctor_set(x_445, 2, x_431);
lean_ctor_set(x_445, 3, x_440);
lean_ctor_set(x_445, 4, x_444);
return x_445;
}
block_454:
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_nat_add(x_447, x_448);
lean_dec(x_448);
lean_dec(x_447);
if (lean_is_scalar(x_7)) {
 x_450 = lean_alloc_ctor(0, 5, 0);
} else {
 x_450 = x_7;
}
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_417);
lean_ctor_set(x_450, 2, x_418);
lean_ctor_set(x_450, 3, x_419);
lean_ctor_set(x_450, 4, x_432);
x_451 = lean_nat_add(x_414, x_415);
lean_dec(x_415);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_452; 
x_452 = lean_ctor_get(x_433, 0);
lean_inc(x_452);
x_440 = x_450;
x_441 = x_451;
x_442 = x_452;
goto block_446;
}
else
{
lean_object* x_453; 
x_453 = lean_unsigned_to_nat(0u);
x_440 = x_450;
x_441 = x_451;
x_442 = x_453;
goto block_446;
}
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; 
lean_dec(x_433);
lean_dec(x_432);
lean_dec(x_431);
lean_dec(x_430);
lean_dec(x_428);
lean_dec(x_7);
x_457 = lean_nat_add(x_414, x_416);
lean_dec(x_416);
x_458 = lean_nat_add(x_457, x_415);
lean_dec(x_457);
x_459 = lean_nat_add(x_414, x_415);
lean_dec(x_415);
x_460 = lean_nat_add(x_459, x_429);
lean_dec(x_429);
lean_dec(x_459);
lean_inc_ref(x_413);
if (lean_is_scalar(x_427)) {
 x_461 = lean_alloc_ctor(0, 5, 0);
} else {
 x_461 = x_427;
}
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_3);
lean_ctor_set(x_461, 2, x_4);
lean_ctor_set(x_461, 3, x_420);
lean_ctor_set(x_461, 4, x_413);
x_462 = !lean_is_exclusive(x_413);
if (x_462 == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_463 = lean_ctor_get(x_413, 4);
lean_dec(x_463);
x_464 = lean_ctor_get(x_413, 3);
lean_dec(x_464);
x_465 = lean_ctor_get(x_413, 2);
lean_dec(x_465);
x_466 = lean_ctor_get(x_413, 1);
lean_dec(x_466);
x_467 = lean_ctor_get(x_413, 0);
lean_dec(x_467);
lean_ctor_set(x_413, 4, x_461);
lean_ctor_set(x_413, 3, x_419);
lean_ctor_set(x_413, 2, x_418);
lean_ctor_set(x_413, 1, x_417);
lean_ctor_set(x_413, 0, x_458);
return x_413;
}
else
{
lean_object* x_468; 
lean_dec(x_413);
x_468 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_468, 0, x_458);
lean_ctor_set(x_468, 1, x_417);
lean_ctor_set(x_468, 2, x_418);
lean_ctor_set(x_468, 3, x_419);
lean_ctor_set(x_468, 4, x_461);
return x_468;
}
}
}
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_469 = lean_ctor_get(x_413, 0);
lean_inc(x_469);
x_470 = lean_nat_add(x_414, x_469);
lean_dec(x_469);
if (lean_is_scalar(x_7)) {
 x_471 = lean_alloc_ctor(0, 5, 0);
} else {
 x_471 = x_7;
}
lean_ctor_set(x_471, 0, x_470);
lean_ctor_set(x_471, 1, x_3);
lean_ctor_set(x_471, 2, x_4);
lean_ctor_set(x_471, 3, x_5);
lean_ctor_set(x_471, 4, x_413);
return x_471;
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_472; 
x_472 = lean_ctor_get(x_5, 3);
lean_inc(x_472);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; 
x_473 = lean_ctor_get(x_5, 4);
lean_inc(x_473);
if (lean_obj_tag(x_473) == 0)
{
uint8_t x_474; 
x_474 = !lean_is_exclusive(x_5);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_475 = lean_ctor_get(x_5, 0);
x_476 = lean_ctor_get(x_5, 1);
x_477 = lean_ctor_get(x_5, 2);
x_478 = lean_ctor_get(x_5, 4);
lean_dec(x_478);
x_479 = lean_ctor_get(x_5, 3);
lean_dec(x_479);
x_480 = lean_ctor_get(x_473, 0);
lean_inc(x_480);
x_481 = lean_nat_add(x_414, x_475);
lean_dec(x_475);
x_482 = lean_nat_add(x_414, x_480);
lean_dec(x_480);
lean_ctor_set(x_5, 4, x_413);
lean_ctor_set(x_5, 3, x_473);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_482);
if (lean_is_scalar(x_7)) {
 x_483 = lean_alloc_ctor(0, 5, 0);
} else {
 x_483 = x_7;
}
lean_ctor_set(x_483, 0, x_481);
lean_ctor_set(x_483, 1, x_476);
lean_ctor_set(x_483, 2, x_477);
lean_ctor_set(x_483, 3, x_472);
lean_ctor_set(x_483, 4, x_5);
return x_483;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_484 = lean_ctor_get(x_5, 0);
x_485 = lean_ctor_get(x_5, 1);
x_486 = lean_ctor_get(x_5, 2);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_5);
x_487 = lean_ctor_get(x_473, 0);
lean_inc(x_487);
x_488 = lean_nat_add(x_414, x_484);
lean_dec(x_484);
x_489 = lean_nat_add(x_414, x_487);
lean_dec(x_487);
x_490 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_490, 0, x_489);
lean_ctor_set(x_490, 1, x_3);
lean_ctor_set(x_490, 2, x_4);
lean_ctor_set(x_490, 3, x_473);
lean_ctor_set(x_490, 4, x_413);
if (lean_is_scalar(x_7)) {
 x_491 = lean_alloc_ctor(0, 5, 0);
} else {
 x_491 = x_7;
}
lean_ctor_set(x_491, 0, x_488);
lean_ctor_set(x_491, 1, x_485);
lean_ctor_set(x_491, 2, x_486);
lean_ctor_set(x_491, 3, x_472);
lean_ctor_set(x_491, 4, x_490);
return x_491;
}
}
else
{
uint8_t x_492; 
x_492 = !lean_is_exclusive(x_5);
if (x_492 == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_493 = lean_ctor_get(x_5, 1);
x_494 = lean_ctor_get(x_5, 2);
x_495 = lean_ctor_get(x_5, 4);
lean_dec(x_495);
x_496 = lean_ctor_get(x_5, 3);
lean_dec(x_496);
x_497 = lean_ctor_get(x_5, 0);
lean_dec(x_497);
x_498 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_5, 3, x_473);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_414);
if (lean_is_scalar(x_7)) {
 x_499 = lean_alloc_ctor(0, 5, 0);
} else {
 x_499 = x_7;
}
lean_ctor_set(x_499, 0, x_498);
lean_ctor_set(x_499, 1, x_493);
lean_ctor_set(x_499, 2, x_494);
lean_ctor_set(x_499, 3, x_472);
lean_ctor_set(x_499, 4, x_5);
return x_499;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_500 = lean_ctor_get(x_5, 1);
x_501 = lean_ctor_get(x_5, 2);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_5);
x_502 = lean_unsigned_to_nat(3u);
x_503 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_503, 0, x_414);
lean_ctor_set(x_503, 1, x_3);
lean_ctor_set(x_503, 2, x_4);
lean_ctor_set(x_503, 3, x_473);
lean_ctor_set(x_503, 4, x_473);
if (lean_is_scalar(x_7)) {
 x_504 = lean_alloc_ctor(0, 5, 0);
} else {
 x_504 = x_7;
}
lean_ctor_set(x_504, 0, x_502);
lean_ctor_set(x_504, 1, x_500);
lean_ctor_set(x_504, 2, x_501);
lean_ctor_set(x_504, 3, x_472);
lean_ctor_set(x_504, 4, x_503);
return x_504;
}
}
}
else
{
lean_object* x_505; 
x_505 = lean_ctor_get(x_5, 4);
lean_inc(x_505);
if (lean_obj_tag(x_505) == 0)
{
uint8_t x_506; 
x_506 = !lean_is_exclusive(x_5);
if (x_506 == 0)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; uint8_t x_512; 
x_507 = lean_ctor_get(x_5, 1);
x_508 = lean_ctor_get(x_5, 2);
x_509 = lean_ctor_get(x_5, 4);
lean_dec(x_509);
x_510 = lean_ctor_get(x_5, 3);
lean_dec(x_510);
x_511 = lean_ctor_get(x_5, 0);
lean_dec(x_511);
x_512 = !lean_is_exclusive(x_505);
if (x_512 == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_513 = lean_ctor_get(x_505, 1);
x_514 = lean_ctor_get(x_505, 2);
x_515 = lean_ctor_get(x_505, 4);
lean_dec(x_515);
x_516 = lean_ctor_get(x_505, 3);
lean_dec(x_516);
x_517 = lean_ctor_get(x_505, 0);
lean_dec(x_517);
x_518 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_505, 4, x_472);
lean_ctor_set(x_505, 3, x_472);
lean_ctor_set(x_505, 2, x_508);
lean_ctor_set(x_505, 1, x_507);
lean_ctor_set(x_505, 0, x_414);
lean_ctor_set(x_5, 4, x_472);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_414);
if (lean_is_scalar(x_7)) {
 x_519 = lean_alloc_ctor(0, 5, 0);
} else {
 x_519 = x_7;
}
lean_ctor_set(x_519, 0, x_518);
lean_ctor_set(x_519, 1, x_513);
lean_ctor_set(x_519, 2, x_514);
lean_ctor_set(x_519, 3, x_505);
lean_ctor_set(x_519, 4, x_5);
return x_519;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_520 = lean_ctor_get(x_505, 1);
x_521 = lean_ctor_get(x_505, 2);
lean_inc(x_521);
lean_inc(x_520);
lean_dec(x_505);
x_522 = lean_unsigned_to_nat(3u);
x_523 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_523, 0, x_414);
lean_ctor_set(x_523, 1, x_507);
lean_ctor_set(x_523, 2, x_508);
lean_ctor_set(x_523, 3, x_472);
lean_ctor_set(x_523, 4, x_472);
lean_ctor_set(x_5, 4, x_472);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_414);
if (lean_is_scalar(x_7)) {
 x_524 = lean_alloc_ctor(0, 5, 0);
} else {
 x_524 = x_7;
}
lean_ctor_set(x_524, 0, x_522);
lean_ctor_set(x_524, 1, x_520);
lean_ctor_set(x_524, 2, x_521);
lean_ctor_set(x_524, 3, x_523);
lean_ctor_set(x_524, 4, x_5);
return x_524;
}
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_525 = lean_ctor_get(x_5, 1);
x_526 = lean_ctor_get(x_5, 2);
lean_inc(x_526);
lean_inc(x_525);
lean_dec(x_5);
x_527 = lean_ctor_get(x_505, 1);
lean_inc(x_527);
x_528 = lean_ctor_get(x_505, 2);
lean_inc(x_528);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 lean_ctor_release(x_505, 2);
 lean_ctor_release(x_505, 3);
 lean_ctor_release(x_505, 4);
 x_529 = x_505;
} else {
 lean_dec_ref(x_505);
 x_529 = lean_box(0);
}
x_530 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_529)) {
 x_531 = lean_alloc_ctor(0, 5, 0);
} else {
 x_531 = x_529;
}
lean_ctor_set(x_531, 0, x_414);
lean_ctor_set(x_531, 1, x_525);
lean_ctor_set(x_531, 2, x_526);
lean_ctor_set(x_531, 3, x_472);
lean_ctor_set(x_531, 4, x_472);
x_532 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_532, 0, x_414);
lean_ctor_set(x_532, 1, x_3);
lean_ctor_set(x_532, 2, x_4);
lean_ctor_set(x_532, 3, x_472);
lean_ctor_set(x_532, 4, x_472);
if (lean_is_scalar(x_7)) {
 x_533 = lean_alloc_ctor(0, 5, 0);
} else {
 x_533 = x_7;
}
lean_ctor_set(x_533, 0, x_530);
lean_ctor_set(x_533, 1, x_527);
lean_ctor_set(x_533, 2, x_528);
lean_ctor_set(x_533, 3, x_531);
lean_ctor_set(x_533, 4, x_532);
return x_533;
}
}
else
{
lean_object* x_534; lean_object* x_535; 
x_534 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_7)) {
 x_535 = lean_alloc_ctor(0, 5, 0);
} else {
 x_535 = x_7;
}
lean_ctor_set(x_535, 0, x_534);
lean_ctor_set(x_535, 1, x_3);
lean_ctor_set(x_535, 2, x_4);
lean_ctor_set(x_535, 3, x_5);
lean_ctor_set(x_535, 4, x_505);
return x_535;
}
}
}
else
{
lean_object* x_536; 
if (lean_is_scalar(x_7)) {
 x_536 = lean_alloc_ctor(0, 5, 0);
} else {
 x_536 = x_7;
}
lean_ctor_set(x_536, 0, x_414);
lean_ctor_set(x_536, 1, x_3);
lean_ctor_set(x_536, 2, x_4);
lean_ctor_set(x_536, 3, x_5);
lean_ctor_set(x_536, 4, x_5);
return x_536;
}
}
}
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
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
return x_6;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557_(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557_(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3_spec__3_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3_spec__3_spec__3___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3_spec__3___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__6___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__6___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__7___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc_ref(x_1);
x_10 = lean_apply_1(x_1, x_3);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_15 = x_4;
} else {
 lean_dec_ref(x_4);
 x_15 = lean_box(0);
}
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_18 = x_11;
} else {
 lean_dec_ref(x_11);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 2);
lean_inc_ref(x_20);
lean_dec(x_12);
x_21 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_20, x_17, x_2, x_9);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = 0;
x_25 = l_Lean_Compiler_LCNF_mkAuxParam(x_22, x_24, x_5, x_6, x_7, x_8, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; uint8_t x_54; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
x_32 = lean_array_push(x_16, x_26);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_31);
x_40 = lean_array_get_size(x_30);
x_41 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557_(x_19);
x_42 = 32;
x_43 = lean_uint64_shift_right(x_41, x_42);
x_44 = lean_uint64_xor(x_41, x_43);
x_45 = 16;
x_46 = lean_uint64_shift_right(x_44, x_45);
x_47 = lean_uint64_xor(x_44, x_46);
x_48 = lean_uint64_to_usize(x_47);
x_49 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_50 = 1;
x_51 = lean_usize_sub(x_49, x_50);
x_52 = lean_usize_land(x_48, x_51);
x_53 = lean_array_uget(x_30, x_52);
x_54 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2___redArg(x_19, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_29, x_55);
lean_dec(x_29);
lean_inc_ref(x_33);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_19);
lean_ctor_set(x_57, 1, x_33);
lean_ctor_set(x_57, 2, x_53);
x_58 = lean_array_uset(x_30, x_52, x_57);
x_59 = lean_unsigned_to_nat(4u);
x_60 = lean_nat_mul(x_56, x_59);
x_61 = lean_unsigned_to_nat(3u);
x_62 = lean_nat_div(x_60, x_61);
lean_dec(x_60);
x_63 = lean_array_get_size(x_58);
x_64 = lean_nat_dec_le(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(x_58);
lean_ctor_set(x_17, 1, x_65);
lean_ctor_set(x_17, 0, x_56);
x_34 = x_17;
goto block_39;
}
else
{
lean_ctor_set(x_17, 1, x_58);
lean_ctor_set(x_17, 0, x_56);
x_34 = x_17;
goto block_39;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_box(0);
x_67 = lean_array_uset(x_30, x_52, x_66);
lean_inc_ref(x_33);
x_68 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__6___redArg(x_19, x_33, x_53);
x_69 = lean_array_uset(x_67, x_52, x_68);
lean_ctor_set(x_17, 1, x_69);
x_34 = x_17;
goto block_39;
}
block_39:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_array_push(x_14, x_33);
if (lean_is_scalar(x_18)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_18;
}
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_34);
if (lean_is_scalar(x_15)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_15;
}
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_3 = x_13;
x_4 = x_37;
x_9 = x_27;
goto _start;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; uint64_t x_87; uint64_t x_88; size_t x_89; size_t x_90; size_t x_91; size_t x_92; size_t x_93; lean_object* x_94; uint8_t x_95; 
x_70 = lean_ctor_get(x_17, 0);
x_71 = lean_ctor_get(x_17, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_17);
x_72 = lean_ctor_get(x_26, 0);
lean_inc(x_72);
x_73 = lean_array_push(x_16, x_26);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_72);
x_81 = lean_array_get_size(x_71);
x_82 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1557_(x_19);
x_83 = 32;
x_84 = lean_uint64_shift_right(x_82, x_83);
x_85 = lean_uint64_xor(x_82, x_84);
x_86 = 16;
x_87 = lean_uint64_shift_right(x_85, x_86);
x_88 = lean_uint64_xor(x_85, x_87);
x_89 = lean_uint64_to_usize(x_88);
x_90 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_91 = 1;
x_92 = lean_usize_sub(x_90, x_91);
x_93 = lean_usize_land(x_89, x_92);
x_94 = lean_array_uget(x_71, x_93);
x_95 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2___redArg(x_19, x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_add(x_70, x_96);
lean_dec(x_70);
lean_inc_ref(x_74);
x_98 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_98, 0, x_19);
lean_ctor_set(x_98, 1, x_74);
lean_ctor_set(x_98, 2, x_94);
x_99 = lean_array_uset(x_71, x_93, x_98);
x_100 = lean_unsigned_to_nat(4u);
x_101 = lean_nat_mul(x_97, x_100);
x_102 = lean_unsigned_to_nat(3u);
x_103 = lean_nat_div(x_101, x_102);
lean_dec(x_101);
x_104 = lean_array_get_size(x_99);
x_105 = lean_nat_dec_le(x_103, x_104);
lean_dec(x_104);
lean_dec(x_103);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(x_99);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_97);
lean_ctor_set(x_107, 1, x_106);
x_75 = x_107;
goto block_80;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_97);
lean_ctor_set(x_108, 1, x_99);
x_75 = x_108;
goto block_80;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_box(0);
x_110 = lean_array_uset(x_71, x_93, x_109);
lean_inc_ref(x_74);
x_111 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__6___redArg(x_19, x_74, x_94);
x_112 = lean_array_uset(x_110, x_93, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_70);
lean_ctor_set(x_113, 1, x_112);
x_75 = x_113;
goto block_80;
}
block_80:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_array_push(x_14, x_74);
if (lean_is_scalar(x_18)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_18;
}
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_75);
if (lean_is_scalar(x_15)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_15;
}
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_3 = x_13;
x_4 = x_78;
x_9 = x_27;
goto _start;
}
}
}
case 1:
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_10, 0);
lean_inc(x_114);
lean_dec_ref(x_10);
x_3 = x_114;
goto _start;
}
default: 
{
lean_object* x_116; 
lean_dec_ref(x_1);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_4);
lean_ctor_set(x_116, 1, x_9);
return x_116;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__7(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__7___redArg(x_1, x_2, x_7, x_8, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_uget(x_4, x_3);
x_14 = lean_unsigned_to_nat(0u);
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
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_26, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
lean_ctor_set(x_13, 2, x_28);
x_16 = x_13;
x_17 = x_29;
goto block_22;
}
else
{
uint8_t x_30; 
lean_free_object(x_13);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
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
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_37 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_36, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
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
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
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
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_47 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_46, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
lean_ctor_set(x_13, 0, x_48);
x_16 = x_13;
x_17 = x_49;
goto block_22;
}
else
{
uint8_t x_50; 
lean_free_object(x_13);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
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
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_55 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_54, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_56);
x_16 = x_58;
x_17 = x_57;
goto block_22;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
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
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__6;
x_2 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__5;
x_3 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__4;
x_4 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__3;
x_5 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__2;
x_6 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_inc_ref(x_15);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_dec(x_18);
x_19 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec_ref(x_17);
x_20 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__7;
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
lean_dec_ref(x_22);
x_24 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__7;
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
lean_inc_ref(x_29);
lean_dec(x_10);
x_30 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_30);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_31 = x_27;
} else {
 lean_dec_ref(x_27);
 x_31 = lean_box(0);
}
x_32 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_30);
lean_dec_ref(x_30);
x_33 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__7;
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
lean_inc_ref(x_43);
lean_dec(x_37);
x_44 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_44);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_45 = x_40;
} else {
 lean_dec_ref(x_40);
 x_45 = lean_box(0);
}
x_46 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_44);
lean_dec_ref(x_44);
x_47 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__7;
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg(x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_fget(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decLt___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__0;
x_2 = lean_alloc_closure((void*)(l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PRange_instUpwardEnumerableNat;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__1;
x_3 = lean_alloc_closure((void*)(l_Std_PRange_instIteratorRangeIteratorIdOfUpwardEnumerableOfSupportsUpperBound___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7;
x_3 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6;
x_4 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5;
x_5 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__10;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12;
x_3 = l_Std_Iterators_Types_Attach_instIterator___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_x", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__14;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_jp", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__17;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_alt", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__19;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__22;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__23;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__24;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__25;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`Code.bind` failed, empty `cases` found", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__27;
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
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_10);
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
lean_inc_ref(x_74);
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
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_226; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec_ref(x_76);
x_79 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lam__0___boxed), 2, 0);
if (lean_obj_tag(x_77) == 0)
{
x_226 = x_77;
goto block_282;
}
else
{
lean_object* x_283; 
x_283 = lean_ctor_get(x_77, 0);
lean_inc(x_283);
lean_dec(x_77);
x_226 = x_283;
goto block_282;
}
block_225:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_87 = l_Array_toSubarray___redArg(x_83, x_85, x_86);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 2);
lean_inc(x_89);
x_90 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lam__2___boxed), 2, 1);
lean_closure_set(x_90, 0, x_87);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_80);
lean_ctor_set(x_91, 1, x_84);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_82);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_88);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_89);
x_95 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12;
x_96 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__13;
lean_inc_ref(x_79);
x_97 = l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(x_79, x_96, x_95);
x_98 = l_Std_Iterators_instIteratorMap___redArg(x_95, x_97, x_79, x_90);
x_99 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__7___redArg(x_98, x_72, x_94, x_92, x_4, x_5, x_6, x_7, x_81);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec_ref(x_99);
x_103 = !lean_is_exclusive(x_100);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_ctor_get(x_100, 0);
x_105 = lean_ctor_get(x_100, 1);
lean_dec(x_105);
x_106 = !lean_is_exclusive(x_101);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_101, 0);
x_108 = lean_ctor_get(x_101, 1);
lean_dec(x_108);
lean_inc(x_73);
if (lean_is_scalar(x_75)) {
 x_109 = lean_alloc_ctor(4, 2, 0);
} else {
 x_109 = x_75;
}
lean_ctor_set(x_109, 0, x_73);
lean_ctor_set(x_109, 1, x_104);
x_110 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_111 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_109, x_110, x_4, x_5, x_6, x_7, x_102);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec_ref(x_111);
x_114 = lean_ctor_get(x_1, 0);
x_115 = lean_ctor_get(x_112, 0);
lean_inc(x_115);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__16;
x_118 = lean_array_push(x_117, x_116);
lean_inc(x_114);
lean_ctor_set_tag(x_101, 3);
lean_ctor_set(x_101, 1, x_118);
lean_ctor_set(x_101, 0, x_114);
lean_ctor_set(x_100, 0, x_112);
x_119 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__18;
x_120 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_107, x_100, x_119, x_4, x_5, x_6, x_7, x_113);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec_ref(x_120);
x_123 = lean_st_ref_take(x_3, x_122);
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_121);
x_127 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_FVarIdSet_insert_spec__1___redArg(x_73, x_121, x_125);
x_128 = lean_st_ref_set(x_3, x_127, x_126);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_128, 0);
lean_dec(x_130);
x_131 = lean_ctor_get(x_121, 0);
lean_inc(x_131);
lean_dec(x_121);
lean_ctor_set_tag(x_123, 3);
lean_ctor_set(x_123, 1, x_74);
lean_ctor_set(x_123, 0, x_131);
lean_ctor_set(x_128, 0, x_123);
return x_128;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
lean_dec(x_128);
x_133 = lean_ctor_get(x_121, 0);
lean_inc(x_133);
lean_dec(x_121);
lean_ctor_set_tag(x_123, 3);
lean_ctor_set(x_123, 1, x_74);
lean_ctor_set(x_123, 0, x_133);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_123);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_135 = lean_ctor_get(x_123, 0);
x_136 = lean_ctor_get(x_123, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_123);
lean_inc(x_121);
x_137 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_FVarIdSet_insert_spec__1___redArg(x_73, x_121, x_135);
x_138 = lean_st_ref_set(x_3, x_137, x_136);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_140 = x_138;
} else {
 lean_dec_ref(x_138);
 x_140 = lean_box(0);
}
x_141 = lean_ctor_get(x_121, 0);
lean_inc(x_141);
lean_dec(x_121);
x_142 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_74);
if (lean_is_scalar(x_140)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_140;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_139);
return x_143;
}
}
else
{
uint8_t x_144; 
lean_dec_ref(x_74);
lean_dec(x_73);
x_144 = !lean_is_exclusive(x_120);
if (x_144 == 0)
{
return x_120;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_120, 0);
x_146 = lean_ctor_get(x_120, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_120);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
lean_free_object(x_101);
lean_dec(x_107);
lean_free_object(x_100);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_148 = !lean_is_exclusive(x_111);
if (x_148 == 0)
{
return x_111;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_111, 0);
x_150 = lean_ctor_get(x_111, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_111);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_101, 0);
lean_inc(x_152);
lean_dec(x_101);
lean_inc(x_73);
if (lean_is_scalar(x_75)) {
 x_153 = lean_alloc_ctor(4, 2, 0);
} else {
 x_153 = x_75;
}
lean_ctor_set(x_153, 0, x_73);
lean_ctor_set(x_153, 1, x_104);
x_154 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_155 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_153, x_154, x_4, x_5, x_6, x_7, x_102);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec_ref(x_155);
x_158 = lean_ctor_get(x_1, 0);
x_159 = lean_ctor_get(x_156, 0);
lean_inc(x_159);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_161 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__16;
x_162 = lean_array_push(x_161, x_160);
lean_inc(x_158);
x_163 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_163, 0, x_158);
lean_ctor_set(x_163, 1, x_162);
lean_ctor_set(x_100, 1, x_163);
lean_ctor_set(x_100, 0, x_156);
x_164 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__18;
x_165 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_152, x_100, x_164, x_4, x_5, x_6, x_7, x_157);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec_ref(x_165);
x_168 = lean_st_ref_take(x_3, x_167);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_171 = x_168;
} else {
 lean_dec_ref(x_168);
 x_171 = lean_box(0);
}
lean_inc(x_166);
x_172 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_FVarIdSet_insert_spec__1___redArg(x_73, x_166, x_169);
x_173 = lean_st_ref_set(x_3, x_172, x_170);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_175 = x_173;
} else {
 lean_dec_ref(x_173);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_166, 0);
lean_inc(x_176);
lean_dec(x_166);
if (lean_is_scalar(x_171)) {
 x_177 = lean_alloc_ctor(3, 2, 0);
} else {
 x_177 = x_171;
 lean_ctor_set_tag(x_177, 3);
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_74);
if (lean_is_scalar(x_175)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_175;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_174);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec_ref(x_74);
lean_dec(x_73);
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
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_152);
lean_free_object(x_100);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_183 = lean_ctor_get(x_155, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_155, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_185 = x_155;
} else {
 lean_dec_ref(x_155);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_187 = lean_ctor_get(x_100, 0);
lean_inc(x_187);
lean_dec(x_100);
x_188 = lean_ctor_get(x_101, 0);
lean_inc(x_188);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_189 = x_101;
} else {
 lean_dec_ref(x_101);
 x_189 = lean_box(0);
}
lean_inc(x_73);
if (lean_is_scalar(x_75)) {
 x_190 = lean_alloc_ctor(4, 2, 0);
} else {
 x_190 = x_75;
}
lean_ctor_set(x_190, 0, x_73);
lean_ctor_set(x_190, 1, x_187);
x_191 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_192 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_190, x_191, x_4, x_5, x_6, x_7, x_102);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec_ref(x_192);
x_195 = lean_ctor_get(x_1, 0);
x_196 = lean_ctor_get(x_193, 0);
lean_inc(x_196);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_198 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__16;
x_199 = lean_array_push(x_198, x_197);
lean_inc(x_195);
if (lean_is_scalar(x_189)) {
 x_200 = lean_alloc_ctor(3, 2, 0);
} else {
 x_200 = x_189;
 lean_ctor_set_tag(x_200, 3);
}
lean_ctor_set(x_200, 0, x_195);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_193);
lean_ctor_set(x_201, 1, x_200);
x_202 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__18;
x_203 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_188, x_201, x_202, x_4, x_5, x_6, x_7, x_194);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec_ref(x_203);
x_206 = lean_st_ref_take(x_3, x_205);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_209 = x_206;
} else {
 lean_dec_ref(x_206);
 x_209 = lean_box(0);
}
lean_inc(x_204);
x_210 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_FVarIdSet_insert_spec__1___redArg(x_73, x_204, x_207);
x_211 = lean_st_ref_set(x_3, x_210, x_208);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_213 = x_211;
} else {
 lean_dec_ref(x_211);
 x_213 = lean_box(0);
}
x_214 = lean_ctor_get(x_204, 0);
lean_inc(x_214);
lean_dec(x_204);
if (lean_is_scalar(x_209)) {
 x_215 = lean_alloc_ctor(3, 2, 0);
} else {
 x_215 = x_209;
 lean_ctor_set_tag(x_215, 3);
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_74);
if (lean_is_scalar(x_213)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_213;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_212);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec_ref(x_74);
lean_dec(x_73);
x_217 = lean_ctor_get(x_203, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_203, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_219 = x_203;
} else {
 lean_dec_ref(x_203);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_217);
lean_ctor_set(x_220, 1, x_218);
return x_220;
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_189);
lean_dec(x_188);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_221 = lean_ctor_get(x_192, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_192, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_223 = x_192;
} else {
 lean_dec_ref(x_192);
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
}
block_282:
{
lean_object* x_227; uint8_t x_228; 
x_227 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__20;
x_228 = lean_name_eq(x_226, x_227);
lean_dec(x_226);
if (x_228 == 0)
{
lean_dec_ref(x_79);
lean_dec(x_75);
lean_dec_ref(x_74);
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
lean_object* x_229; lean_object* x_230; 
lean_inc(x_73);
x_229 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___redArg(x_73, x_5, x_78);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; 
lean_dec_ref(x_79);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec_ref(x_229);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_231;
goto block_68;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
lean_dec(x_11);
lean_dec_ref(x_10);
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
lean_dec_ref(x_229);
x_233 = lean_ctor_get(x_230, 0);
lean_inc(x_233);
lean_dec_ref(x_230);
x_234 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_9, x_5, x_232);
lean_dec_ref(x_9);
x_235 = !lean_is_exclusive(x_234);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_236 = lean_ctor_get(x_234, 1);
x_237 = lean_ctor_get(x_234, 0);
lean_dec(x_237);
x_238 = lean_st_ref_get(x_3, x_236);
x_239 = !lean_is_exclusive(x_238);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_238, 0);
x_241 = lean_ctor_get(x_238, 1);
x_242 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_240, x_73);
lean_dec(x_240);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
lean_free_object(x_238);
lean_free_object(x_234);
x_243 = lean_ctor_get(x_233, 2);
lean_inc_ref(x_243);
lean_dec(x_233);
x_244 = lean_unsigned_to_nat(0u);
x_245 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__21;
x_246 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__26;
x_247 = lean_array_get_size(x_74);
x_248 = lean_array_get_size(x_243);
x_249 = lean_nat_dec_le(x_247, x_248);
if (x_249 == 0)
{
lean_dec(x_247);
x_80 = x_245;
x_81 = x_241;
x_82 = x_245;
x_83 = x_243;
x_84 = x_246;
x_85 = x_244;
x_86 = x_248;
goto block_225;
}
else
{
lean_dec(x_248);
x_80 = x_245;
x_81 = x_241;
x_82 = x_245;
x_83 = x_243;
x_84 = x_246;
x_85 = x_244;
x_86 = x_247;
goto block_225;
}
}
else
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_233);
lean_dec_ref(x_79);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_250 = lean_ctor_get(x_242, 0);
lean_inc(x_250);
lean_dec_ref(x_242);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
lean_dec(x_250);
lean_ctor_set_tag(x_234, 3);
lean_ctor_set(x_234, 1, x_74);
lean_ctor_set(x_234, 0, x_251);
lean_ctor_set(x_238, 0, x_234);
return x_238;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_238, 0);
x_253 = lean_ctor_get(x_238, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_238);
x_254 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_252, x_73);
lean_dec(x_252);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
lean_free_object(x_234);
x_255 = lean_ctor_get(x_233, 2);
lean_inc_ref(x_255);
lean_dec(x_233);
x_256 = lean_unsigned_to_nat(0u);
x_257 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__21;
x_258 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__26;
x_259 = lean_array_get_size(x_74);
x_260 = lean_array_get_size(x_255);
x_261 = lean_nat_dec_le(x_259, x_260);
if (x_261 == 0)
{
lean_dec(x_259);
x_80 = x_257;
x_81 = x_253;
x_82 = x_257;
x_83 = x_255;
x_84 = x_258;
x_85 = x_256;
x_86 = x_260;
goto block_225;
}
else
{
lean_dec(x_260);
x_80 = x_257;
x_81 = x_253;
x_82 = x_257;
x_83 = x_255;
x_84 = x_258;
x_85 = x_256;
x_86 = x_259;
goto block_225;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_233);
lean_dec_ref(x_79);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_262 = lean_ctor_get(x_254, 0);
lean_inc(x_262);
lean_dec_ref(x_254);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
lean_dec(x_262);
lean_ctor_set_tag(x_234, 3);
lean_ctor_set(x_234, 1, x_74);
lean_ctor_set(x_234, 0, x_263);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_234);
lean_ctor_set(x_264, 1, x_253);
return x_264;
}
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_265 = lean_ctor_get(x_234, 1);
lean_inc(x_265);
lean_dec(x_234);
x_266 = lean_st_ref_get(x_3, x_265);
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
x_270 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_267, x_73);
lean_dec(x_267);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
lean_dec(x_269);
x_271 = lean_ctor_get(x_233, 2);
lean_inc_ref(x_271);
lean_dec(x_233);
x_272 = lean_unsigned_to_nat(0u);
x_273 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__21;
x_274 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__26;
x_275 = lean_array_get_size(x_74);
x_276 = lean_array_get_size(x_271);
x_277 = lean_nat_dec_le(x_275, x_276);
if (x_277 == 0)
{
lean_dec(x_275);
x_80 = x_273;
x_81 = x_268;
x_82 = x_273;
x_83 = x_271;
x_84 = x_274;
x_85 = x_272;
x_86 = x_276;
goto block_225;
}
else
{
lean_dec(x_276);
x_80 = x_273;
x_81 = x_268;
x_82 = x_273;
x_83 = x_271;
x_84 = x_274;
x_85 = x_272;
x_86 = x_275;
goto block_225;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_233);
lean_dec_ref(x_79);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_278 = lean_ctor_get(x_270, 0);
lean_inc(x_278);
lean_dec_ref(x_270);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
lean_dec(x_278);
x_280 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_74);
if (lean_is_scalar(x_269)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_269;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_268);
return x_281;
}
}
}
}
}
}
else
{
uint8_t x_284; 
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_284 = !lean_is_exclusive(x_76);
if (x_284 == 0)
{
return x_76;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_76, 0);
x_286 = lean_ctor_get(x_76, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_76);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
return x_287;
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
lean_dec_ref(x_18);
x_21 = lean_st_ref_get(x_12, x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_9, 0);
lean_inc(x_25);
x_26 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_23, x_25);
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
lean_dec_ref(x_26);
x_29 = lean_st_ref_take(x_12, x_24);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_25, x_31);
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
x_43 = l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_25, x_41);
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
x_53 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_50, x_52);
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
lean_dec_ref(x_53);
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
x_61 = l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_52, x_58);
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
lean_dec_ref(x_9);
return x_18;
}
}
}
case 1:
{
uint8_t x_288; 
x_288 = !lean_is_exclusive(x_2);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_2, 0);
x_290 = lean_ctor_get(x_2, 1);
x_291 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_290, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_291) == 0)
{
uint8_t x_292; 
x_292 = !lean_is_exclusive(x_291);
if (x_292 == 0)
{
lean_object* x_293; 
x_293 = lean_ctor_get(x_291, 0);
lean_ctor_set(x_2, 1, x_293);
lean_ctor_set(x_291, 0, x_2);
return x_291;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_291, 0);
x_295 = lean_ctor_get(x_291, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_291);
lean_ctor_set(x_2, 1, x_294);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_2);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
else
{
lean_free_object(x_2);
lean_dec_ref(x_289);
return x_291;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_2, 0);
x_298 = lean_ctor_get(x_2, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_2);
x_299 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_298, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_302 = x_299;
} else {
 lean_dec_ref(x_299);
 x_302 = lean_box(0);
}
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_297);
lean_ctor_set(x_303, 1, x_300);
if (lean_is_scalar(x_302)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_302;
}
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_301);
return x_304;
}
else
{
lean_dec_ref(x_297);
return x_299;
}
}
}
case 2:
{
uint8_t x_305; 
x_305 = !lean_is_exclusive(x_2);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_306 = lean_ctor_get(x_2, 0);
x_307 = lean_ctor_get(x_2, 1);
x_308 = lean_ctor_get(x_306, 2);
lean_inc_ref(x_308);
x_309 = lean_ctor_get(x_306, 4);
lean_inc_ref(x_309);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_310 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_309, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec_ref(x_310);
lean_inc(x_311);
lean_inc_ref(x_308);
x_313 = l_Lean_Compiler_LCNF_Code_inferParamType(x_308, x_311, x_4, x_5, x_6, x_7, x_312);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec_ref(x_313);
x_316 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_306, x_314, x_308, x_311, x_5, x_315);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec_ref(x_316);
x_319 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_307, x_3, x_4, x_5, x_6, x_7, x_318);
if (lean_obj_tag(x_319) == 0)
{
uint8_t x_320; 
x_320 = !lean_is_exclusive(x_319);
if (x_320 == 0)
{
lean_object* x_321; 
x_321 = lean_ctor_get(x_319, 0);
lean_ctor_set(x_2, 1, x_321);
lean_ctor_set(x_2, 0, x_317);
lean_ctor_set(x_319, 0, x_2);
return x_319;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_319, 0);
x_323 = lean_ctor_get(x_319, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_319);
lean_ctor_set(x_2, 1, x_322);
lean_ctor_set(x_2, 0, x_317);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_2);
lean_ctor_set(x_324, 1, x_323);
return x_324;
}
}
else
{
lean_dec(x_317);
lean_free_object(x_2);
return x_319;
}
}
else
{
uint8_t x_325; 
lean_dec(x_311);
lean_dec_ref(x_308);
lean_free_object(x_2);
lean_dec_ref(x_307);
lean_dec_ref(x_306);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_325 = !lean_is_exclusive(x_313);
if (x_325 == 0)
{
return x_313;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_313, 0);
x_327 = lean_ctor_get(x_313, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_313);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
}
else
{
lean_dec_ref(x_308);
lean_free_object(x_2);
lean_dec_ref(x_307);
lean_dec_ref(x_306);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_310;
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_329 = lean_ctor_get(x_2, 0);
x_330 = lean_ctor_get(x_2, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_2);
x_331 = lean_ctor_get(x_329, 2);
lean_inc_ref(x_331);
x_332 = lean_ctor_get(x_329, 4);
lean_inc_ref(x_332);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_333 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_332, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
lean_dec_ref(x_333);
lean_inc(x_334);
lean_inc_ref(x_331);
x_336 = l_Lean_Compiler_LCNF_Code_inferParamType(x_331, x_334, x_4, x_5, x_6, x_7, x_335);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec_ref(x_336);
x_339 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_329, x_337, x_331, x_334, x_5, x_338);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec_ref(x_339);
x_342 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_330, x_3, x_4, x_5, x_6, x_7, x_341);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_345 = x_342;
} else {
 lean_dec_ref(x_342);
 x_345 = lean_box(0);
}
x_346 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_346, 0, x_340);
lean_ctor_set(x_346, 1, x_343);
if (lean_is_scalar(x_345)) {
 x_347 = lean_alloc_ctor(0, 2, 0);
} else {
 x_347 = x_345;
}
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_344);
return x_347;
}
else
{
lean_dec(x_340);
return x_342;
}
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_334);
lean_dec_ref(x_331);
lean_dec_ref(x_330);
lean_dec_ref(x_329);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_348 = lean_ctor_get(x_336, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_336, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_350 = x_336;
} else {
 lean_dec_ref(x_336);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(1, 2, 0);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_348);
lean_ctor_set(x_351, 1, x_349);
return x_351;
}
}
else
{
lean_dec_ref(x_331);
lean_dec_ref(x_330);
lean_dec_ref(x_329);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_333;
}
}
}
case 4:
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; size_t x_358; size_t x_359; lean_object* x_360; 
x_352 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_352);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_353 = x_2;
} else {
 lean_dec_ref(x_2);
 x_353 = lean_box(0);
}
x_354 = lean_ctor_get(x_352, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_352, 2);
lean_inc(x_355);
x_356 = lean_ctor_get(x_352, 3);
lean_inc_ref(x_356);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 lean_ctor_release(x_352, 2);
 lean_ctor_release(x_352, 3);
 x_357 = x_352;
} else {
 lean_dec_ref(x_352);
 x_357 = lean_box(0);
}
x_358 = lean_array_size(x_356);
x_359 = 0;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_360 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__8(x_1, x_358, x_359, x_356, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_383; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec_ref(x_360);
x_383 = l_Array_isEmpty___redArg(x_361);
if (x_383 == 0)
{
x_363 = x_4;
x_364 = x_5;
x_365 = x_6;
x_366 = x_7;
x_367 = x_362;
goto block_382;
}
else
{
lean_object* x_384; lean_object* x_385; uint8_t x_386; 
lean_dec(x_361);
lean_dec(x_357);
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_353);
lean_dec_ref(x_4);
x_384 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__28;
x_385 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg(x_384, x_5, x_6, x_7, x_362);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_386 = !lean_is_exclusive(x_385);
if (x_386 == 0)
{
return x_385;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_385, 0);
x_388 = lean_ctor_get(x_385, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_385);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
return x_389;
}
}
block_382:
{
lean_object* x_368; 
lean_inc(x_361);
x_368 = l_Lean_Compiler_LCNF_mkCasesResultType(x_361, x_363, x_364, x_365, x_366, x_367);
lean_dec(x_366);
lean_dec_ref(x_365);
lean_dec(x_364);
lean_dec_ref(x_363);
if (lean_obj_tag(x_368) == 0)
{
uint8_t x_369; 
x_369 = !lean_is_exclusive(x_368);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_368, 0);
if (lean_is_scalar(x_357)) {
 x_371 = lean_alloc_ctor(0, 4, 0);
} else {
 x_371 = x_357;
}
lean_ctor_set(x_371, 0, x_354);
lean_ctor_set(x_371, 1, x_370);
lean_ctor_set(x_371, 2, x_355);
lean_ctor_set(x_371, 3, x_361);
if (lean_is_scalar(x_353)) {
 x_372 = lean_alloc_ctor(4, 1, 0);
} else {
 x_372 = x_353;
}
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_368, 0, x_372);
return x_368;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_373 = lean_ctor_get(x_368, 0);
x_374 = lean_ctor_get(x_368, 1);
lean_inc(x_374);
lean_inc(x_373);
lean_dec(x_368);
if (lean_is_scalar(x_357)) {
 x_375 = lean_alloc_ctor(0, 4, 0);
} else {
 x_375 = x_357;
}
lean_ctor_set(x_375, 0, x_354);
lean_ctor_set(x_375, 1, x_373);
lean_ctor_set(x_375, 2, x_355);
lean_ctor_set(x_375, 3, x_361);
if (lean_is_scalar(x_353)) {
 x_376 = lean_alloc_ctor(4, 1, 0);
} else {
 x_376 = x_353;
}
lean_ctor_set(x_376, 0, x_375);
x_377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_374);
return x_377;
}
}
else
{
uint8_t x_378; 
lean_dec(x_361);
lean_dec(x_357);
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_353);
x_378 = !lean_is_exclusive(x_368);
if (x_378 == 0)
{
return x_368;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_368, 0);
x_380 = lean_ctor_get(x_368, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_368);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
return x_381;
}
}
}
}
else
{
uint8_t x_390; 
lean_dec(x_357);
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_390 = !lean_is_exclusive(x_360);
if (x_390 == 0)
{
return x_360;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_360, 0);
x_392 = lean_ctor_get(x_360, 1);
lean_inc(x_392);
lean_inc(x_391);
lean_dec(x_360);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
return x_393;
}
}
}
case 5:
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_394 = lean_ctor_get(x_2, 0);
lean_inc(x_394);
lean_dec_ref(x_2);
x_395 = lean_ctor_get(x_1, 0);
x_396 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_396, 0, x_394);
x_397 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__16;
x_398 = lean_array_push(x_397, x_396);
lean_inc(x_395);
x_399 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_399, 0, x_395);
lean_ctor_set(x_399, 1, x_398);
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_8);
return x_400;
}
default: 
{
lean_object* x_401; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_2);
lean_ctor_set(x_401, 1, x_8);
return x_401;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__7___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_2);
x_18 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__7(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__8(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec_ref(x_1);
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
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_uget(x_4, x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_4, x_3, x_14);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_30);
x_16 = x_30;
goto block_29;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_31);
x_16 = x_31;
goto block_29;
}
block_29:
{
lean_object* x_17; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_16, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
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
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
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
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 2);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0_spec__0(x_1, x_4);
lean_inc(x_3);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_box(1);
x_9 = lean_st_mk_ref(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
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
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(x_1, x_15, x_10, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
x_28 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0_spec__0(x_27, x_22);
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
x_32 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0_spec__0(x_31, x_22);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
x_45 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0_spec__0(x_44, x_38);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
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
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_59 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(x_1, x_58, x_10, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec_ref(x_59);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
x_72 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0_spec__0(x_71, x_63);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___Std_DTreeMap_Internal_Impl_foldl___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldl___at___Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_20; 
x_20 = lean_usize_dec_eq(x_2, x_3);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_array_uget(x_1, x_2);
switch (lean_obj_tag(x_21)) {
case 2:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_22);
lean_dec_ref(x_21);
x_23 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_22, x_5, x_6);
lean_dec_ref(x_22);
x_7 = x_23;
goto block_13;
}
case 3:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_24);
lean_dec_ref(x_21);
x_25 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_25, x_5, x_6);
lean_dec_ref(x_25);
x_7 = x_26;
goto block_13;
}
case 4:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_27);
lean_dec_ref(x_21);
x_28 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_27, x_5, x_6);
lean_dec_ref(x_27);
x_7 = x_28;
goto block_13;
}
default: 
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_29);
lean_dec_ref(x_21);
x_14 = x_29;
x_15 = x_5;
x_16 = x_6;
goto block_19;
}
}
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_6);
return x_30;
}
block_13:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_8;
x_6 = x_9;
goto _start;
}
block_19:
{
uint8_t x_17; lean_object* x_18; 
x_17 = 1;
x_18 = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(x_14, x_17, x_15, x_16);
lean_dec_ref(x_14);
x_7 = x_18;
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_inc_ref(x_27);
lean_dec_ref(x_26);
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
lean_inc_ref(x_30);
lean_dec_ref(x_26);
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
lean_inc_ref(x_31);
lean_dec_ref(x_26);
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
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_35);
lean_dec_ref(x_26);
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
x_38 = lean_name_eq(x_37, x_36);
lean_dec(x_36);
lean_dec(x_37);
if (x_38 == 0)
{
lean_dec_ref(x_35);
lean_dec_ref(x_34);
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
lean_dec_ref(x_34);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
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
lean_dec_ref(x_34);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec_ref(x_45);
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
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_50);
lean_dec_ref(x_26);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 2);
lean_inc_ref(x_53);
lean_inc_ref(x_53);
x_54 = l_Lean_Expr_headBeta(x_53);
x_55 = l_Lean_Expr_isForall(x_54);
lean_dec_ref(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_2);
x_56 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__18;
x_57 = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(x_49, x_3, x_56, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec_ref(x_57);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_60 = l_Lean_Compiler_LCNF_ToLCNF_bindCases(x_58, x_50, x_4, x_5, x_6, x_7, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_2 = x_25;
x_3 = x_61;
x_8 = x_62;
goto _start;
}
else
{
lean_dec(x_25);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_60;
}
}
else
{
uint8_t x_64; 
lean_dec_ref(x_50);
lean_dec(x_25);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
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
lean_dec_ref(x_49);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = lean_st_ref_take(x_5, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec_ref(x_70);
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_71, 0);
x_75 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__21;
x_76 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_76, 0, x_50);
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_51);
lean_ctor_set(x_77, 1, x_52);
lean_ctor_set(x_77, 2, x_75);
lean_ctor_set(x_77, 3, x_53);
lean_ctor_set(x_77, 4, x_76);
lean_inc_ref(x_77);
x_78 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_74, x_77);
lean_ctor_set(x_71, 0, x_78);
x_79 = lean_st_ref_set(x_5, x_71, x_72);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec_ref(x_79);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_81 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_77, x_4, x_5, x_6, x_7, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec_ref(x_81);
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
x_90 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__21;
x_91 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_91, 0, x_50);
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_51);
lean_ctor_set(x_92, 1, x_52);
lean_ctor_set(x_92, 2, x_90);
lean_ctor_set(x_92, 3, x_53);
lean_ctor_set(x_92, 4, x_91);
lean_inc_ref(x_92);
x_93 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_88, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_89);
x_95 = lean_st_ref_set(x_5, x_94, x_72);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec_ref(x_95);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_97 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_92, x_4, x_5, x_6, x_7, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec_ref(x_97);
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_inc_ref(x_3);
x_105 = l_Lean_Compiler_LCNF_Code_inferType(x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_130; uint8_t x_131; 
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
lean_dec_ref(x_3);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec_ref(x_113);
x_130 = lean_array_get_size(x_1);
x_131 = lean_nat_dec_le(x_2, x_130);
if (x_131 == 0)
{
lean_dec(x_2);
x_115 = x_20;
x_116 = x_130;
goto block_129;
}
else
{
lean_dec(x_130);
x_115 = x_20;
x_116 = x_2;
goto block_129;
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
block_129:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_117 = l_Array_toSubarray___redArg(x_1, x_115, x_116);
x_118 = lean_ctor_get(x_117, 0);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 2);
lean_inc(x_120);
lean_dec_ref(x_117);
x_121 = lean_nat_dec_lt(x_119, x_120);
if (x_121 == 0)
{
lean_dec(x_120);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec(x_5);
x_109 = x_114;
goto block_112;
}
else
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_array_get_size(x_118);
x_123 = lean_nat_dec_le(x_120, x_122);
lean_dec(x_122);
if (x_123 == 0)
{
lean_dec(x_120);
lean_dec(x_119);
lean_dec_ref(x_118);
lean_dec(x_5);
x_109 = x_114;
goto block_112;
}
else
{
lean_object* x_124; size_t x_125; size_t x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_box(0);
x_125 = lean_usize_of_nat(x_119);
lean_dec(x_119);
x_126 = lean_usize_of_nat(x_120);
lean_dec(x_120);
x_127 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___redArg(x_118, x_125, x_126, x_124, x_5, x_114);
lean_dec(x_5);
lean_dec_ref(x_118);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec_ref(x_127);
x_109 = x_128;
goto block_112;
}
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_104);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_132 = !lean_is_exclusive(x_105);
if (x_132 == 0)
{
return x_105;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_105, 0);
x_134 = lean_ctor_get(x_105, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_105);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
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
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__0;
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
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__0;
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
x_2 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__1;
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
x_3 = lean_box(1);
x_4 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__4;
x_5 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__7;
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
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12() {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_st_ref_get(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_box(1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_12 = lean_st_mk_ref(x_11, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_15);
lean_dec(x_7);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_17 = 0;
x_18 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_9);
lean_ctor_set(x_21, 2, x_15);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set(x_21, 4, x_19);
lean_ctor_set(x_21, 5, x_10);
lean_ctor_set(x_21, 6, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*7, x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*7 + 1, x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*7 + 2, x_17);
lean_inc(x_13);
x_22 = lean_apply_5(x_1, x_21, x_13, x_3, x_4, x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_st_ref_get(x_13, x_24);
lean_dec(x_13);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_23);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_dec(x_13);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_box(1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_15 = lean_st_mk_ref(x_14, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_18);
lean_dec(x_10);
x_19 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_20 = 0;
x_21 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_22 = lean_box(0);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_12);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set(x_24, 5, x_13);
lean_ctor_set(x_24, 6, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*7, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*7 + 1, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*7 + 2, x_20);
lean_inc(x_16);
x_25 = lean_apply_5(x_2, x_24, x_16, x_6, x_7, x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_st_ref_get(x_16, x_27);
lean_dec(x_16);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_dec(x_16);
return x_25;
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
lean_dec_ref(x_4);
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
lean_dec_ref(x_4);
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
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get_uint8(x_5, sizeof(void*)*6);
x_20 = lean_ctor_get(x_5, 2);
x_21 = lean_ctor_get(x_5, 3);
x_22 = lean_ctor_get(x_5, 4);
x_23 = lean_ctor_get(x_5, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_24 = lean_array_push(x_22, x_1);
x_25 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set(x_25, 5, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*6, x_19);
x_26 = lean_st_ref_set(x_2, x_25, x_6);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = 0;
x_9 = l_Lean_Compiler_LCNF_mkAuxParam(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
lean_inc(x_10);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_12, x_2, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_inc_ref(x_38);
x_39 = lean_array_get_size(x_38);
lean_dec_ref(x_38);
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
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
lean_dec_ref(x_15);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_1);
x_18 = l_Lean_Compiler_LCNF_LetValue_inferType(x_1, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = l_Lean_Compiler_LCNF_mkLetDecl(x_16, x_19, x_1, x_10, x_11, x_12, x_13, x_20);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
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
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
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
lean_dec_ref(x_1);
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
x_24 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_25 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_23, x_24, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_18);
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
x_1 = lean_box(1);
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
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__24;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(1);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__9;
x_3 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__8;
x_4 = 1;
x_5 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__6;
x_6 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__5;
x_7 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_3);
lean_ctor_set(x_7, 4, x_2);
lean_ctor_set(x_7, 5, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*6, x_4);
return x_7;
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
lean_dec_ref(x_8);
lean_inc(x_9);
x_11 = lean_apply_6(x_1, x_9, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
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
uint8_t x_3; 
lean_dec_ref(x_1);
x_3 = 0;
return x_3;
}
case 3:
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = 1;
return x_4;
}
case 7:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 2);
x_2 = x_5;
goto _start;
}
case 8:
{
uint8_t x_7; 
lean_dec_ref(x_1);
x_7 = 2;
return x_7;
}
case 10:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 1);
x_2 = x_8;
goto _start;
}
default: 
{
lean_object* x_10; 
x_10 = l_Lean_Expr_getAppFn(x_2);
switch (lean_obj_tag(x_10)) {
case 0:
{
uint8_t x_11; 
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_11 = 0;
return x_11;
}
case 4:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = 0;
x_14 = l_Lean_Environment_find_x3f(x_1, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = 2;
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec_ref(x_14);
if (lean_obj_tag(x_16) == 5)
{
uint8_t x_17; 
lean_dec_ref(x_16);
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_16);
x_18 = 2;
return x_18;
}
}
}
default: 
{
uint8_t x_19; 
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_19 = 2;
return x_19;
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
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Expr_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_expr_eqv(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__4___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_expr_eqv(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__4___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_expr_eqv(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__5___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_24; lean_object* x_25; lean_object* x_109; uint8_t x_110; 
x_109 = lean_st_ref_get(x_4, x_5);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ctor_get(x_109, 1);
x_113 = lean_ctor_get(x_111, 0);
lean_inc_ref(x_113);
lean_dec(x_111);
x_114 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(x_113, x_1);
switch (x_114) {
case 0:
{
uint8_t x_115; lean_object* x_116; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_115 = 0;
x_116 = lean_box(x_115);
lean_ctor_set(x_109, 0, x_116);
return x_109;
}
case 1:
{
uint8_t x_117; lean_object* x_118; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_117 = 1;
x_118 = lean_box(x_117);
lean_ctor_set(x_109, 0, x_118);
return x_109;
}
default: 
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_free_object(x_109);
x_119 = lean_st_ref_get(x_2, x_112);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_120, 3);
lean_inc_ref(x_121);
lean_dec(x_120);
x_122 = !lean_is_exclusive(x_119);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint64_t x_127; uint64_t x_128; uint64_t x_129; uint64_t x_130; uint64_t x_131; uint64_t x_132; uint64_t x_133; size_t x_134; size_t x_135; size_t x_136; size_t x_137; size_t x_138; lean_object* x_139; lean_object* x_140; 
x_123 = lean_ctor_get(x_119, 1);
x_124 = lean_ctor_get(x_119, 0);
lean_dec(x_124);
x_125 = lean_ctor_get(x_121, 1);
lean_inc_ref(x_125);
lean_dec_ref(x_121);
x_126 = lean_array_get_size(x_125);
x_127 = l_Lean_Expr_hash(x_1);
x_128 = 32;
x_129 = lean_uint64_shift_right(x_127, x_128);
x_130 = lean_uint64_xor(x_127, x_129);
x_131 = 16;
x_132 = lean_uint64_shift_right(x_130, x_131);
x_133 = lean_uint64_xor(x_130, x_132);
x_134 = lean_uint64_to_usize(x_133);
x_135 = lean_usize_of_nat(x_126);
lean_dec(x_126);
x_136 = 1;
x_137 = lean_usize_sub(x_135, x_136);
x_138 = lean_usize_land(x_134, x_137);
x_139 = lean_array_uget(x_125, x_138);
lean_dec_ref(x_125);
x_140 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__5___redArg(x_1, x_139);
lean_dec(x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_free_object(x_119);
x_141 = lean_st_ref_get(x_2, x_123);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec_ref(x_141);
x_144 = lean_box(1);
x_145 = lean_unsigned_to_nat(0u);
x_146 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_147 = lean_st_mk_ref(x_146, x_143);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec_ref(x_147);
x_150 = lean_ctor_get(x_142, 0);
lean_inc_ref(x_150);
lean_dec(x_142);
x_151 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_152 = 0;
x_153 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_154 = lean_box(0);
x_155 = lean_box(0);
x_156 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_156, 0, x_151);
lean_ctor_set(x_156, 1, x_144);
lean_ctor_set(x_156, 2, x_150);
lean_ctor_set(x_156, 3, x_153);
lean_ctor_set(x_156, 4, x_154);
lean_ctor_set(x_156, 5, x_145);
lean_ctor_set(x_156, 6, x_155);
lean_ctor_set_uint8(x_156, sizeof(void*)*7, x_152);
lean_ctor_set_uint8(x_156, sizeof(void*)*7 + 1, x_152);
lean_ctor_set_uint8(x_156, sizeof(void*)*7 + 2, x_152);
lean_inc(x_148);
lean_inc_ref(x_1);
x_157 = l_Lean_Meta_isTypeFormerType(x_1, x_156, x_148, x_3, x_4, x_149);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec_ref(x_157);
x_160 = lean_st_ref_get(x_148, x_159);
lean_dec(x_148);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec_ref(x_160);
x_162 = lean_unbox(x_158);
lean_dec(x_158);
x_24 = x_162;
x_25 = x_161;
goto block_108;
}
else
{
lean_dec(x_148);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_163 = lean_ctor_get(x_157, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_157, 1);
lean_inc(x_164);
lean_dec_ref(x_157);
x_165 = lean_unbox(x_163);
lean_dec(x_163);
x_24 = x_165;
x_25 = x_164;
goto block_108;
}
else
{
lean_dec_ref(x_1);
return x_157;
}
}
}
else
{
lean_object* x_166; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_166 = lean_ctor_get(x_140, 0);
lean_inc(x_166);
lean_dec_ref(x_140);
lean_ctor_set(x_119, 0, x_166);
return x_119;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint64_t x_170; uint64_t x_171; uint64_t x_172; uint64_t x_173; uint64_t x_174; uint64_t x_175; uint64_t x_176; size_t x_177; size_t x_178; size_t x_179; size_t x_180; size_t x_181; lean_object* x_182; lean_object* x_183; 
x_167 = lean_ctor_get(x_119, 1);
lean_inc(x_167);
lean_dec(x_119);
x_168 = lean_ctor_get(x_121, 1);
lean_inc_ref(x_168);
lean_dec_ref(x_121);
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
lean_dec_ref(x_168);
x_183 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__5___redArg(x_1, x_182);
lean_dec(x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_184 = lean_st_ref_get(x_2, x_167);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec_ref(x_184);
x_187 = lean_box(1);
x_188 = lean_unsigned_to_nat(0u);
x_189 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_190 = lean_st_mk_ref(x_189, x_186);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec_ref(x_190);
x_193 = lean_ctor_get(x_185, 0);
lean_inc_ref(x_193);
lean_dec(x_185);
x_194 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_195 = 0;
x_196 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_197 = lean_box(0);
x_198 = lean_box(0);
x_199 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_199, 0, x_194);
lean_ctor_set(x_199, 1, x_187);
lean_ctor_set(x_199, 2, x_193);
lean_ctor_set(x_199, 3, x_196);
lean_ctor_set(x_199, 4, x_197);
lean_ctor_set(x_199, 5, x_188);
lean_ctor_set(x_199, 6, x_198);
lean_ctor_set_uint8(x_199, sizeof(void*)*7, x_195);
lean_ctor_set_uint8(x_199, sizeof(void*)*7 + 1, x_195);
lean_ctor_set_uint8(x_199, sizeof(void*)*7 + 2, x_195);
lean_inc(x_191);
lean_inc_ref(x_1);
x_200 = l_Lean_Meta_isTypeFormerType(x_1, x_199, x_191, x_3, x_4, x_192);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec_ref(x_200);
x_203 = lean_st_ref_get(x_191, x_202);
lean_dec(x_191);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec_ref(x_203);
x_205 = lean_unbox(x_201);
lean_dec(x_201);
x_24 = x_205;
x_25 = x_204;
goto block_108;
}
else
{
lean_dec(x_191);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_206 = lean_ctor_get(x_200, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_200, 1);
lean_inc(x_207);
lean_dec_ref(x_200);
x_208 = lean_unbox(x_206);
lean_dec(x_206);
x_24 = x_208;
x_25 = x_207;
goto block_108;
}
else
{
lean_dec_ref(x_1);
return x_200;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_209 = lean_ctor_get(x_183, 0);
lean_inc(x_209);
lean_dec_ref(x_183);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_167);
return x_210;
}
}
}
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_211 = lean_ctor_get(x_109, 0);
x_212 = lean_ctor_get(x_109, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_109);
x_213 = lean_ctor_get(x_211, 0);
lean_inc_ref(x_213);
lean_dec(x_211);
x_214 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(x_213, x_1);
switch (x_214) {
case 0:
{
uint8_t x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_215 = 0;
x_216 = lean_box(x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_212);
return x_217;
}
case 1:
{
uint8_t x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_218 = 1;
x_219 = lean_box(x_218);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_212);
return x_220;
}
default: 
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint64_t x_228; uint64_t x_229; uint64_t x_230; uint64_t x_231; uint64_t x_232; uint64_t x_233; uint64_t x_234; size_t x_235; size_t x_236; size_t x_237; size_t x_238; size_t x_239; lean_object* x_240; lean_object* x_241; 
x_221 = lean_st_ref_get(x_2, x_212);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_222, 3);
lean_inc_ref(x_223);
lean_dec(x_222);
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_225 = x_221;
} else {
 lean_dec_ref(x_221);
 x_225 = lean_box(0);
}
x_226 = lean_ctor_get(x_223, 1);
lean_inc_ref(x_226);
lean_dec_ref(x_223);
x_227 = lean_array_get_size(x_226);
x_228 = l_Lean_Expr_hash(x_1);
x_229 = 32;
x_230 = lean_uint64_shift_right(x_228, x_229);
x_231 = lean_uint64_xor(x_228, x_230);
x_232 = 16;
x_233 = lean_uint64_shift_right(x_231, x_232);
x_234 = lean_uint64_xor(x_231, x_233);
x_235 = lean_uint64_to_usize(x_234);
x_236 = lean_usize_of_nat(x_227);
lean_dec(x_227);
x_237 = 1;
x_238 = lean_usize_sub(x_236, x_237);
x_239 = lean_usize_land(x_235, x_238);
x_240 = lean_array_uget(x_226, x_239);
lean_dec_ref(x_226);
x_241 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__5___redArg(x_1, x_240);
lean_dec(x_240);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_225);
x_242 = lean_st_ref_get(x_2, x_224);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec_ref(x_242);
x_245 = lean_box(1);
x_246 = lean_unsigned_to_nat(0u);
x_247 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_248 = lean_st_mk_ref(x_247, x_244);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec_ref(x_248);
x_251 = lean_ctor_get(x_243, 0);
lean_inc_ref(x_251);
lean_dec(x_243);
x_252 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_253 = 0;
x_254 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_255 = lean_box(0);
x_256 = lean_box(0);
x_257 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_257, 0, x_252);
lean_ctor_set(x_257, 1, x_245);
lean_ctor_set(x_257, 2, x_251);
lean_ctor_set(x_257, 3, x_254);
lean_ctor_set(x_257, 4, x_255);
lean_ctor_set(x_257, 5, x_246);
lean_ctor_set(x_257, 6, x_256);
lean_ctor_set_uint8(x_257, sizeof(void*)*7, x_253);
lean_ctor_set_uint8(x_257, sizeof(void*)*7 + 1, x_253);
lean_ctor_set_uint8(x_257, sizeof(void*)*7 + 2, x_253);
lean_inc(x_249);
lean_inc_ref(x_1);
x_258 = l_Lean_Meta_isTypeFormerType(x_1, x_257, x_249, x_3, x_4, x_250);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec_ref(x_258);
x_261 = lean_st_ref_get(x_249, x_260);
lean_dec(x_249);
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
lean_dec_ref(x_261);
x_263 = lean_unbox(x_259);
lean_dec(x_259);
x_24 = x_263;
x_25 = x_262;
goto block_108;
}
else
{
lean_dec(x_249);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_264 = lean_ctor_get(x_258, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_258, 1);
lean_inc(x_265);
lean_dec_ref(x_258);
x_266 = lean_unbox(x_264);
lean_dec(x_264);
x_24 = x_266;
x_25 = x_265;
goto block_108;
}
else
{
lean_dec_ref(x_1);
return x_258;
}
}
}
else
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_267 = lean_ctor_get(x_241, 0);
lean_inc(x_267);
lean_dec_ref(x_241);
if (lean_is_scalar(x_225)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_225;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_224);
return x_268;
}
}
}
}
block_23:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set(x_15, 4, x_9);
lean_ctor_set(x_15, 5, x_7);
lean_ctor_set_uint8(x_15, sizeof(void*)*6, x_10);
x_16 = lean_st_ref_set(x_2, x_15, x_13);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(x_8);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
block_108:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_26 = lean_st_ref_take(x_2, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 3);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec_ref(x_26);
x_30 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_31);
x_32 = lean_ctor_get_uint8(x_27, sizeof(void*)*6);
x_33 = lean_ctor_get(x_27, 2);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_27, 4);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_27, 5);
lean_inc(x_35);
lean_dec(x_27);
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
x_39 = lean_array_get_size(x_38);
x_40 = l_Lean_Expr_hash(x_1);
x_41 = 32;
x_42 = lean_uint64_shift_right(x_40, x_41);
x_43 = lean_uint64_xor(x_40, x_42);
x_44 = 16;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_49 = 1;
x_50 = lean_usize_sub(x_48, x_49);
x_51 = lean_usize_land(x_47, x_50);
x_52 = lean_array_uget(x_38, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0___redArg(x_1, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_37, x_54);
lean_dec(x_37);
x_56 = lean_box(x_24);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_52);
x_58 = lean_array_uset(x_38, x_51, x_57);
x_59 = lean_unsigned_to_nat(4u);
x_60 = lean_nat_mul(x_55, x_59);
x_61 = lean_unsigned_to_nat(3u);
x_62 = lean_nat_div(x_60, x_61);
lean_dec(x_60);
x_63 = lean_array_get_size(x_58);
x_64 = lean_nat_dec_le(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1___redArg(x_58);
lean_ctor_set(x_28, 1, x_65);
lean_ctor_set(x_28, 0, x_55);
x_6 = x_31;
x_7 = x_35;
x_8 = x_24;
x_9 = x_34;
x_10 = x_32;
x_11 = x_30;
x_12 = x_33;
x_13 = x_29;
x_14 = x_28;
goto block_23;
}
else
{
lean_ctor_set(x_28, 1, x_58);
lean_ctor_set(x_28, 0, x_55);
x_6 = x_31;
x_7 = x_35;
x_8 = x_24;
x_9 = x_34;
x_10 = x_32;
x_11 = x_30;
x_12 = x_33;
x_13 = x_29;
x_14 = x_28;
goto block_23;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_box(0);
x_67 = lean_array_uset(x_38, x_51, x_66);
x_68 = lean_box(x_24);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__4___redArg(x_1, x_68, x_52);
x_70 = lean_array_uset(x_67, x_51, x_69);
lean_ctor_set(x_28, 1, x_70);
x_6 = x_31;
x_7 = x_35;
x_8 = x_24;
x_9 = x_34;
x_10 = x_32;
x_11 = x_30;
x_12 = x_33;
x_13 = x_29;
x_14 = x_28;
goto block_23;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; size_t x_81; size_t x_82; size_t x_83; size_t x_84; size_t x_85; lean_object* x_86; uint8_t x_87; 
x_71 = lean_ctor_get(x_28, 0);
x_72 = lean_ctor_get(x_28, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_28);
x_73 = lean_array_get_size(x_72);
x_74 = l_Lean_Expr_hash(x_1);
x_75 = 32;
x_76 = lean_uint64_shift_right(x_74, x_75);
x_77 = lean_uint64_xor(x_74, x_76);
x_78 = 16;
x_79 = lean_uint64_shift_right(x_77, x_78);
x_80 = lean_uint64_xor(x_77, x_79);
x_81 = lean_uint64_to_usize(x_80);
x_82 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_83 = 1;
x_84 = lean_usize_sub(x_82, x_83);
x_85 = lean_usize_land(x_81, x_84);
x_86 = lean_array_uget(x_72, x_85);
x_87 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0___redArg(x_1, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_add(x_71, x_88);
lean_dec(x_71);
x_90 = lean_box(x_24);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_1);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_91, 2, x_86);
x_92 = lean_array_uset(x_72, x_85, x_91);
x_93 = lean_unsigned_to_nat(4u);
x_94 = lean_nat_mul(x_89, x_93);
x_95 = lean_unsigned_to_nat(3u);
x_96 = lean_nat_div(x_94, x_95);
lean_dec(x_94);
x_97 = lean_array_get_size(x_92);
x_98 = lean_nat_dec_le(x_96, x_97);
lean_dec(x_97);
lean_dec(x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1___redArg(x_92);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_89);
lean_ctor_set(x_100, 1, x_99);
x_6 = x_31;
x_7 = x_35;
x_8 = x_24;
x_9 = x_34;
x_10 = x_32;
x_11 = x_30;
x_12 = x_33;
x_13 = x_29;
x_14 = x_100;
goto block_23;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_89);
lean_ctor_set(x_101, 1, x_92);
x_6 = x_31;
x_7 = x_35;
x_8 = x_24;
x_9 = x_34;
x_10 = x_32;
x_11 = x_30;
x_12 = x_33;
x_13 = x_29;
x_14 = x_101;
goto block_23;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_box(0);
x_103 = lean_array_uset(x_72, x_85, x_102);
x_104 = lean_box(x_24);
x_105 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__4___redArg(x_1, x_104, x_86);
x_106 = lean_array_uset(x_103, x_85, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_71);
lean_ctor_set(x_107, 1, x_106);
x_6 = x_31;
x_7 = x_35;
x_8 = x_24;
x_9 = x_34;
x_10 = x_32;
x_11 = x_30;
x_12 = x_33;
x_13 = x_29;
x_14 = x_107;
goto block_23;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__5___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__5(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
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
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_st_ref_get(x_1, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_10, 2);
lean_inc_ref(x_15);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_13, 5);
lean_dec(x_17);
x_18 = lean_ctor_get(x_13, 4);
lean_dec(x_18);
x_19 = lean_ctor_get(x_13, 2);
lean_dec(x_19);
x_20 = lean_ctor_get(x_13, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
lean_ctor_set(x_13, 5, x_6);
lean_ctor_set(x_13, 4, x_5);
lean_ctor_set(x_13, 2, x_15);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set_uint8(x_13, sizeof(void*)*6, x_4);
x_22 = lean_st_ref_set(x_1, x_13, x_14);
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
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_13, 3);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set(x_28, 2, x_15);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_28, 4, x_5);
lean_ctor_set(x_28, 5, x_6);
lean_ctor_set_uint8(x_28, sizeof(void*)*6, x_4);
x_29 = lean_st_ref_set(x_1, x_28, x_14);
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
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
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
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_12, 4);
lean_dec(x_15);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__9;
lean_ctor_set(x_12, 4, x_16);
x_17 = lean_st_ref_set(x_2, x_12, x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_20);
x_21 = lean_ctor_get_uint8(x_9, sizeof(void*)*6);
x_22 = lean_ctor_get(x_9, 4);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_9, 5);
lean_inc(x_23);
lean_dec(x_9);
lean_inc(x_2);
x_24 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
lean_inc(x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_25);
x_28 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(x_2, x_19, x_20, x_21, x_22, x_23, x_27, x_26);
lean_dec_ref(x_27);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_25);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_24, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_dec_ref(x_24);
x_35 = lean_box(0);
x_36 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(x_2, x_19, x_20, x_21, x_22, x_23, x_35, x_34);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 0, x_33);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get_uint8(x_12, sizeof(void*)*6);
x_44 = lean_ctor_get(x_12, 2);
x_45 = lean_ctor_get(x_12, 3);
x_46 = lean_ctor_get(x_12, 5);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_47 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__9;
x_48 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_42);
lean_ctor_set(x_48, 2, x_44);
lean_ctor_set(x_48, 3, x_45);
lean_ctor_set(x_48, 4, x_47);
lean_ctor_set(x_48, 5, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*6, x_43);
x_49 = lean_st_ref_set(x_2, x_48, x_13);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_52);
x_53 = lean_ctor_get_uint8(x_9, sizeof(void*)*6);
x_54 = lean_ctor_get(x_9, 4);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_9, 5);
lean_inc(x_55);
lean_dec(x_9);
lean_inc(x_2);
x_56 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_50);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec_ref(x_56);
lean_inc(x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_57);
x_60 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(x_2, x_51, x_52, x_53, x_54, x_55, x_59, x_58);
lean_dec_ref(x_59);
lean_dec(x_2);
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
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_56, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_56, 1);
lean_inc(x_65);
lean_dec_ref(x_56);
x_66 = lean_box(0);
x_67 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(x_2, x_51, x_52, x_53, x_54, x_55, x_66, x_65);
lean_dec(x_2);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
 lean_ctor_set_tag(x_70, 1);
}
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_68);
return x_70;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l_Lean_Name_quickCmp(x_1, x_3);
switch (x_6) {
case 0:
{
x_2 = x_4;
goto _start;
}
case 1:
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
default: 
{
x_2 = x_5;
goto _start;
}
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_anyExpr;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__0;
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
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___redArg(x_3, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__1;
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
lean_dec_ref(x_8);
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
lean_dec_ref(x_13);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
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
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_22; lean_object* x_23; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_106 = lean_st_ref_get(x_2, x_5);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 2);
lean_inc_ref(x_108);
lean_dec(x_107);
x_109 = !lean_is_exclusive(x_106);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; uint64_t x_118; uint64_t x_119; uint64_t x_120; size_t x_121; size_t x_122; size_t x_123; size_t x_124; size_t x_125; lean_object* x_126; lean_object* x_127; 
x_110 = lean_ctor_get(x_106, 1);
x_111 = lean_ctor_get(x_106, 0);
lean_dec(x_111);
x_112 = lean_ctor_get(x_108, 1);
lean_inc_ref(x_112);
lean_dec_ref(x_108);
x_113 = lean_array_get_size(x_112);
x_114 = l_Lean_Expr_hash(x_1);
x_115 = 32;
x_116 = lean_uint64_shift_right(x_114, x_115);
x_117 = lean_uint64_xor(x_114, x_116);
x_118 = 16;
x_119 = lean_uint64_shift_right(x_117, x_118);
x_120 = lean_uint64_xor(x_117, x_119);
x_121 = lean_uint64_to_usize(x_120);
x_122 = lean_usize_of_nat(x_113);
lean_dec(x_113);
x_123 = 1;
x_124 = lean_usize_sub(x_122, x_123);
x_125 = lean_usize_land(x_121, x_124);
x_126 = lean_array_uget(x_112, x_125);
lean_dec_ref(x_112);
x_127 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__5___redArg(x_1, x_126);
lean_dec(x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_free_object(x_106);
x_128 = lean_st_ref_get(x_2, x_110);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec_ref(x_128);
x_131 = lean_box(1);
x_132 = lean_unsigned_to_nat(0u);
x_133 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_134 = lean_st_mk_ref(x_133, x_130);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec_ref(x_134);
x_137 = lean_ctor_get(x_129, 0);
lean_inc_ref(x_137);
lean_dec(x_129);
x_138 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_139 = 0;
x_140 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_141 = lean_box(0);
x_142 = lean_box(0);
x_143 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_143, 0, x_138);
lean_ctor_set(x_143, 1, x_131);
lean_ctor_set(x_143, 2, x_137);
lean_ctor_set(x_143, 3, x_140);
lean_ctor_set(x_143, 4, x_141);
lean_ctor_set(x_143, 5, x_132);
lean_ctor_set(x_143, 6, x_142);
lean_ctor_set_uint8(x_143, sizeof(void*)*7, x_139);
lean_ctor_set_uint8(x_143, sizeof(void*)*7 + 1, x_139);
lean_ctor_set_uint8(x_143, sizeof(void*)*7 + 2, x_139);
lean_inc(x_135);
lean_inc_ref(x_1);
x_144 = l_Lean_Compiler_LCNF_toLCNFType(x_1, x_143, x_135, x_3, x_4, x_136);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec_ref(x_144);
x_147 = lean_st_ref_get(x_135, x_146);
lean_dec(x_135);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec_ref(x_147);
x_22 = x_145;
x_23 = x_148;
goto block_105;
}
else
{
lean_dec(x_135);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_144, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_144, 1);
lean_inc(x_150);
lean_dec_ref(x_144);
x_22 = x_149;
x_23 = x_150;
goto block_105;
}
else
{
lean_dec_ref(x_1);
return x_144;
}
}
}
else
{
lean_object* x_151; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_151 = lean_ctor_get(x_127, 0);
lean_inc(x_151);
lean_dec_ref(x_127);
lean_ctor_set(x_106, 0, x_151);
return x_106;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint64_t x_155; uint64_t x_156; uint64_t x_157; uint64_t x_158; uint64_t x_159; uint64_t x_160; uint64_t x_161; size_t x_162; size_t x_163; size_t x_164; size_t x_165; size_t x_166; lean_object* x_167; lean_object* x_168; 
x_152 = lean_ctor_get(x_106, 1);
lean_inc(x_152);
lean_dec(x_106);
x_153 = lean_ctor_get(x_108, 1);
lean_inc_ref(x_153);
lean_dec_ref(x_108);
x_154 = lean_array_get_size(x_153);
x_155 = l_Lean_Expr_hash(x_1);
x_156 = 32;
x_157 = lean_uint64_shift_right(x_155, x_156);
x_158 = lean_uint64_xor(x_155, x_157);
x_159 = 16;
x_160 = lean_uint64_shift_right(x_158, x_159);
x_161 = lean_uint64_xor(x_158, x_160);
x_162 = lean_uint64_to_usize(x_161);
x_163 = lean_usize_of_nat(x_154);
lean_dec(x_154);
x_164 = 1;
x_165 = lean_usize_sub(x_163, x_164);
x_166 = lean_usize_land(x_162, x_165);
x_167 = lean_array_uget(x_153, x_166);
lean_dec_ref(x_153);
x_168 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__5___redArg(x_1, x_167);
lean_dec(x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_169 = lean_st_ref_get(x_2, x_152);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec_ref(x_169);
x_172 = lean_box(1);
x_173 = lean_unsigned_to_nat(0u);
x_174 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_175 = lean_st_mk_ref(x_174, x_171);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec_ref(x_175);
x_178 = lean_ctor_get(x_170, 0);
lean_inc_ref(x_178);
lean_dec(x_170);
x_179 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_180 = 0;
x_181 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_182 = lean_box(0);
x_183 = lean_box(0);
x_184 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_184, 0, x_179);
lean_ctor_set(x_184, 1, x_172);
lean_ctor_set(x_184, 2, x_178);
lean_ctor_set(x_184, 3, x_181);
lean_ctor_set(x_184, 4, x_182);
lean_ctor_set(x_184, 5, x_173);
lean_ctor_set(x_184, 6, x_183);
lean_ctor_set_uint8(x_184, sizeof(void*)*7, x_180);
lean_ctor_set_uint8(x_184, sizeof(void*)*7 + 1, x_180);
lean_ctor_set_uint8(x_184, sizeof(void*)*7 + 2, x_180);
lean_inc(x_176);
lean_inc_ref(x_1);
x_185 = l_Lean_Compiler_LCNF_toLCNFType(x_1, x_184, x_176, x_3, x_4, x_177);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec_ref(x_185);
x_188 = lean_st_ref_get(x_176, x_187);
lean_dec(x_176);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec_ref(x_188);
x_22 = x_186;
x_23 = x_189;
goto block_105;
}
else
{
lean_dec(x_176);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_185, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_185, 1);
lean_inc(x_191);
lean_dec_ref(x_185);
x_22 = x_190;
x_23 = x_191;
goto block_105;
}
else
{
lean_dec_ref(x_1);
return x_185;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_192 = lean_ctor_get(x_168, 0);
lean_inc(x_192);
lean_dec_ref(x_168);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_152);
return x_193;
}
}
block_21:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_9);
lean_ctor_set(x_15, 4, x_13);
lean_ctor_set(x_15, 5, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*6, x_10);
x_16 = lean_st_ref_set(x_2, x_15, x_7);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
block_105:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_24 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(x_22, x_2, x_23);
lean_dec_ref(x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_st_ref_take(x_2, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 2);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec_ref(x_27);
x_31 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_32);
x_33 = lean_ctor_get_uint8(x_28, sizeof(void*)*6);
x_34 = lean_ctor_get(x_28, 3);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_28, 4);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_28, 5);
lean_inc(x_36);
lean_dec(x_28);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; uint8_t x_54; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
x_40 = lean_array_get_size(x_39);
x_41 = l_Lean_Expr_hash(x_1);
x_42 = 32;
x_43 = lean_uint64_shift_right(x_41, x_42);
x_44 = lean_uint64_xor(x_41, x_43);
x_45 = 16;
x_46 = lean_uint64_shift_right(x_44, x_45);
x_47 = lean_uint64_xor(x_44, x_46);
x_48 = lean_uint64_to_usize(x_47);
x_49 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_50 = 1;
x_51 = lean_usize_sub(x_49, x_50);
x_52 = lean_usize_land(x_48, x_51);
x_53 = lean_array_uget(x_39, x_52);
x_54 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0___redArg(x_1, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_38, x_55);
lean_dec(x_38);
lean_inc(x_25);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_25);
lean_ctor_set(x_57, 2, x_53);
x_58 = lean_array_uset(x_39, x_52, x_57);
x_59 = lean_unsigned_to_nat(4u);
x_60 = lean_nat_mul(x_56, x_59);
x_61 = lean_unsigned_to_nat(3u);
x_62 = lean_nat_div(x_60, x_61);
lean_dec(x_60);
x_63 = lean_array_get_size(x_58);
x_64 = lean_nat_dec_le(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1___redArg(x_58);
lean_ctor_set(x_29, 1, x_65);
lean_ctor_set(x_29, 0, x_56);
x_6 = x_32;
x_7 = x_30;
x_8 = x_31;
x_9 = x_34;
x_10 = x_33;
x_11 = x_36;
x_12 = x_25;
x_13 = x_35;
x_14 = x_29;
goto block_21;
}
else
{
lean_ctor_set(x_29, 1, x_58);
lean_ctor_set(x_29, 0, x_56);
x_6 = x_32;
x_7 = x_30;
x_8 = x_31;
x_9 = x_34;
x_10 = x_33;
x_11 = x_36;
x_12 = x_25;
x_13 = x_35;
x_14 = x_29;
goto block_21;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_box(0);
x_67 = lean_array_uset(x_39, x_52, x_66);
lean_inc(x_25);
x_68 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__4___redArg(x_1, x_25, x_53);
x_69 = lean_array_uset(x_67, x_52, x_68);
lean_ctor_set(x_29, 1, x_69);
x_6 = x_32;
x_7 = x_30;
x_8 = x_31;
x_9 = x_34;
x_10 = x_33;
x_11 = x_36;
x_12 = x_25;
x_13 = x_35;
x_14 = x_29;
goto block_21;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; size_t x_80; size_t x_81; size_t x_82; size_t x_83; size_t x_84; lean_object* x_85; uint8_t x_86; 
x_70 = lean_ctor_get(x_29, 0);
x_71 = lean_ctor_get(x_29, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_29);
x_72 = lean_array_get_size(x_71);
x_73 = l_Lean_Expr_hash(x_1);
x_74 = 32;
x_75 = lean_uint64_shift_right(x_73, x_74);
x_76 = lean_uint64_xor(x_73, x_75);
x_77 = 16;
x_78 = lean_uint64_shift_right(x_76, x_77);
x_79 = lean_uint64_xor(x_76, x_78);
x_80 = lean_uint64_to_usize(x_79);
x_81 = lean_usize_of_nat(x_72);
lean_dec(x_72);
x_82 = 1;
x_83 = lean_usize_sub(x_81, x_82);
x_84 = lean_usize_land(x_80, x_83);
x_85 = lean_array_uget(x_71, x_84);
x_86 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0___redArg(x_1, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_add(x_70, x_87);
lean_dec(x_70);
lean_inc(x_25);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_25);
lean_ctor_set(x_89, 2, x_85);
x_90 = lean_array_uset(x_71, x_84, x_89);
x_91 = lean_unsigned_to_nat(4u);
x_92 = lean_nat_mul(x_88, x_91);
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
x_97 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1___redArg(x_90);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_88);
lean_ctor_set(x_98, 1, x_97);
x_6 = x_32;
x_7 = x_30;
x_8 = x_31;
x_9 = x_34;
x_10 = x_33;
x_11 = x_36;
x_12 = x_25;
x_13 = x_35;
x_14 = x_98;
goto block_21;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_88);
lean_ctor_set(x_99, 1, x_90);
x_6 = x_32;
x_7 = x_30;
x_8 = x_31;
x_9 = x_34;
x_10 = x_33;
x_11 = x_36;
x_12 = x_25;
x_13 = x_35;
x_14 = x_99;
goto block_21;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_box(0);
x_101 = lean_array_uset(x_71, x_84, x_100);
lean_inc(x_25);
x_102 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__4___redArg(x_1, x_25, x_85);
x_103 = lean_array_uset(x_101, x_84, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_70);
lean_ctor_set(x_104, 1, x_103);
x_6 = x_32;
x_7 = x_30;
x_8 = x_31;
x_9 = x_34;
x_10 = x_33;
x_11 = x_36;
x_12 = x_25;
x_13 = x_35;
x_14 = x_104;
goto block_21;
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
lean_dec_ref(x_3);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_2);
x_12 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_2, x_3, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Lean_isMarkedBorrowed(x_2);
lean_inc(x_10);
x_16 = l_Lean_Compiler_LCNF_mkParam(x_10, x_13, x_15, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_st_ref_take(x_3, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
x_25 = 0;
x_26 = 0;
x_27 = l_Lean_LocalContext_mkLocalDecl(x_23, x_24, x_10, x_2, x_25, x_26);
lean_ctor_set(x_20, 0, x_27);
x_28 = lean_st_ref_set(x_3, x_20, x_21);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_17);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_17);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
x_35 = lean_ctor_get_uint8(x_20, sizeof(void*)*6);
x_36 = lean_ctor_get(x_20, 2);
x_37 = lean_ctor_get(x_20, 3);
x_38 = lean_ctor_get(x_20, 4);
x_39 = lean_ctor_get(x_20, 5);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_40 = lean_ctor_get(x_17, 0);
lean_inc(x_40);
x_41 = 0;
x_42 = 0;
x_43 = l_Lean_LocalContext_mkLocalDecl(x_33, x_40, x_10, x_2, x_41, x_42);
x_44 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_34);
lean_ctor_set(x_44, 2, x_36);
lean_ctor_set(x_44, 3, x_37);
lean_ctor_set(x_44, 4, x_38);
lean_ctor_set(x_44, 5, x_39);
lean_ctor_set_uint8(x_44, sizeof(void*)*6, x_35);
x_45 = lean_st_ref_set(x_3, x_44, x_21);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_17);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_49 = !lean_is_exclusive(x_12);
if (x_49 == 0)
{
return x_12;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_12, 0);
x_51 = lean_ctor_get(x_12, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_12);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
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
lean_dec_ref(x_4);
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
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_5, 0);
x_62 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___closed__0;
lean_inc(x_61);
lean_ctor_set_tag(x_12, 4);
lean_ctor_set(x_12, 1, x_62);
lean_ctor_set(x_12, 0, x_61);
x_16 = x_12;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
goto block_60;
}
else
{
lean_object* x_63; 
lean_free_object(x_12);
x_63 = lean_box(1);
x_16 = x_63;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
goto block_60;
}
block_60:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_inc(x_14);
x_22 = l_Lean_Compiler_LCNF_mkLetDecl(x_14, x_4, x_16, x_18, x_19, x_20, x_21, x_15);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_st_ref_take(x_17, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 4);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
x_32 = 0;
x_33 = 0;
x_34 = l_Lean_LocalContext_mkLetDecl(x_29, x_31, x_14, x_2, x_3, x_32, x_33);
lean_inc(x_23);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_23);
x_36 = lean_array_push(x_30, x_35);
lean_ctor_set(x_26, 4, x_36);
lean_ctor_set(x_26, 0, x_34);
x_37 = lean_st_ref_set(x_17, x_26, x_27);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_23);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_42 = lean_ctor_get(x_26, 0);
x_43 = lean_ctor_get(x_26, 1);
x_44 = lean_ctor_get_uint8(x_26, sizeof(void*)*6);
x_45 = lean_ctor_get(x_26, 2);
x_46 = lean_ctor_get(x_26, 3);
x_47 = lean_ctor_get(x_26, 4);
x_48 = lean_ctor_get(x_26, 5);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_26);
x_49 = lean_ctor_get(x_23, 0);
lean_inc(x_49);
x_50 = 0;
x_51 = 0;
x_52 = l_Lean_LocalContext_mkLetDecl(x_42, x_49, x_14, x_2, x_3, x_50, x_51);
lean_inc(x_23);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_23);
x_54 = lean_array_push(x_47, x_53);
x_55 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_43);
lean_ctor_set(x_55, 2, x_45);
lean_ctor_set(x_55, 3, x_46);
lean_ctor_set(x_55, 4, x_54);
lean_ctor_set(x_55, 5, x_48);
lean_ctor_set_uint8(x_55, sizeof(void*)*6, x_44);
x_56 = lean_st_ref_set(x_17, x_55, x_27);
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
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_23);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_ctor_get(x_12, 0);
x_65 = lean_ctor_get(x_12, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_12);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_5, 0);
x_99 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___closed__0;
lean_inc(x_98);
x_100 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_66 = x_100;
x_67 = x_6;
x_68 = x_7;
x_69 = x_8;
x_70 = x_9;
x_71 = x_10;
goto block_97;
}
else
{
lean_object* x_101; 
x_101 = lean_box(1);
x_66 = x_101;
x_67 = x_6;
x_68 = x_7;
x_69 = x_8;
x_70 = x_9;
x_71 = x_10;
goto block_97;
}
block_97:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_inc(x_64);
x_72 = l_Lean_Compiler_LCNF_mkLetDecl(x_64, x_4, x_66, x_68, x_69, x_70, x_71, x_65);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_75 = lean_st_ref_take(x_67, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_78 = lean_ctor_get(x_76, 0);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_76, 1);
lean_inc_ref(x_79);
x_80 = lean_ctor_get_uint8(x_76, sizeof(void*)*6);
x_81 = lean_ctor_get(x_76, 2);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_76, 3);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_76, 4);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_76, 5);
lean_inc(x_84);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 lean_ctor_release(x_76, 2);
 lean_ctor_release(x_76, 3);
 lean_ctor_release(x_76, 4);
 lean_ctor_release(x_76, 5);
 x_85 = x_76;
} else {
 lean_dec_ref(x_76);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_73, 0);
lean_inc(x_86);
x_87 = 0;
x_88 = 0;
x_89 = l_Lean_LocalContext_mkLetDecl(x_78, x_86, x_64, x_2, x_3, x_87, x_88);
lean_inc(x_73);
x_90 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_90, 0, x_73);
x_91 = lean_array_push(x_83, x_90);
if (lean_is_scalar(x_85)) {
 x_92 = lean_alloc_ctor(0, 6, 1);
} else {
 x_92 = x_85;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_79);
lean_ctor_set(x_92, 2, x_81);
lean_ctor_set(x_92, 3, x_82);
lean_ctor_set(x_92, 4, x_91);
lean_ctor_set(x_92, 5, x_84);
lean_ctor_set_uint8(x_92, sizeof(void*)*6, x_80);
x_93 = lean_st_ref_set(x_67, x_92, x_77);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_73);
lean_ctor_set(x_96, 1, x_94);
return x_96;
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
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
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
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_expr_instantiate_rev(x_11, x_2);
lean_dec_ref(x_11);
lean_inc(x_8);
lean_inc_ref(x_7);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_mkParam(x_10, x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
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
lean_dec_ref(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_7);
x_25 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_5);
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
lean_dec_ref(x_3);
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
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_15);
lean_dec_ref(x_1);
x_16 = lean_expr_instantiate_rev(x_14, x_3);
lean_dec_ref(x_14);
lean_inc(x_9);
lean_inc_ref(x_8);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_mkParam(x_13, x_16, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
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
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_8);
lean_dec(x_2);
x_30 = lean_expr_instantiate_rev(x_1, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
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
lean_dec_ref(x_8);
lean_dec(x_2);
x_33 = lean_expr_instantiate_rev(x_1, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
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
lean_dec_ref(x_6);
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
lean_dec_ref(x_4);
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
lean_object* x_4; uint8_t x_5; uint8_t x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_13 = 0;
lean_inc(x_4);
lean_inc_ref(x_1);
x_14 = l_Lean_Environment_find_x3f(x_1, x_4, x_13);
if (lean_obj_tag(x_14) == 0)
{
goto block_12;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
switch (lean_obj_tag(x_15)) {
case 4:
{
uint8_t x_16; 
lean_dec_ref(x_15);
lean_dec(x_4);
lean_dec_ref(x_1);
x_16 = 1;
return x_16;
}
case 6:
{
uint8_t x_17; 
lean_dec_ref(x_15);
lean_dec(x_4);
lean_dec_ref(x_1);
x_17 = 1;
return x_17;
}
case 7:
{
uint8_t x_18; 
lean_dec_ref(x_15);
lean_dec(x_4);
lean_dec_ref(x_1);
x_18 = 1;
return x_18;
}
default: 
{
lean_dec(x_15);
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
lean_dec_ref(x_1);
return x_5;
}
}
block_12:
{
uint8_t x_10; 
lean_inc(x_4);
lean_inc_ref(x_1);
x_10 = l_Lean_isCasesOnRecursor(x_1, x_4);
if (x_10 == 0)
{
uint8_t x_11; 
lean_inc(x_4);
lean_inc_ref(x_1);
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
uint8_t x_19; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_19 = 0;
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg___lam__0), 8, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___redArg(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = l_Lean_mkAppN(x_1, x_4);
x_12 = 1;
x_13 = l_Lean_Meta_mkLambdaFVars(x_4, x_11, x_2, x_3, x_2, x_3, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_9 = lean_st_ref_get(x_3, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_box(1);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_14 = lean_st_mk_ref(x_13, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_26 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_26);
lean_dec(x_10);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_28 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_29 = lean_box(0);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_12);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 3, x_28);
lean_ctor_set(x_31, 4, x_29);
lean_ctor_set(x_31, 5, x_7);
lean_ctor_set(x_31, 6, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*7, x_8);
lean_ctor_set_uint8(x_31, sizeof(void*)*7 + 1, x_8);
lean_ctor_set_uint8(x_31, sizeof(void*)*7 + 2, x_8);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_15);
lean_inc_ref(x_31);
lean_inc_ref(x_1);
x_32 = lean_infer_type(x_1, x_31, x_15, x_4, x_5, x_16);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = 1;
x_36 = lean_box(x_8);
x_37 = lean_box(x_35);
x_38 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0___boxed), 10, 3);
lean_closure_set(x_38, 0, x_1);
lean_closure_set(x_38, 1, x_36);
lean_closure_set(x_38, 2, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_2);
lean_inc(x_15);
x_40 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg(x_33, x_39, x_38, x_8, x_8, x_31, x_15, x_4, x_5, x_34);
x_17 = x_40;
goto block_25;
}
else
{
lean_dec_ref(x_31);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_17 = x_32;
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
lean_dec_ref(x_17);
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
lean_object* x_41; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_6);
return x_41;
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_5);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0(x_1, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_3);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
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
lean_dec_ref(x_4);
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
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_6 = l_Lean_BinderInfo_isImplicit(x_5);
if (x_6 == 0)
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_7; uint8_t x_8; uint8_t x_19; 
lean_inc_ref(x_4);
x_7 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit(x_4);
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_eq(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_dec_ref(x_31);
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
lean_dec_ref(x_31);
goto block_18;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_expr_lower_loose_bvars(x_31, x_36, x_36);
lean_dec_ref(x_31);
return x_37;
}
}
else
{
lean_dec_ref(x_31);
goto block_18;
}
}
}
else
{
lean_dec_ref(x_30);
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
lean_dec_ref(x_1);
x_9 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_411_(x_5, x_5);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec_ref(x_1);
x_11 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_11;
}
else
{
lean_dec_ref(x_7);
lean_dec_ref(x_3);
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
lean_dec_ref(x_4);
x_8 = x_14;
goto block_12;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = lean_ptr_addr(x_4);
lean_dec_ref(x_4);
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
lean_dec_ref(x_1);
x_20 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_411_(x_5, x_5);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec_ref(x_1);
x_22 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_22;
}
else
{
lean_dec_ref(x_7);
lean_dec_ref(x_3);
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
lean_dec_ref(x_4);
x_19 = x_25;
goto block_23;
}
else
{
size_t x_26; size_t x_27; uint8_t x_28; 
x_26 = lean_ptr_addr(x_4);
lean_dec_ref(x_4);
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
x_10 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15;
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
lean_dec_ref(x_4);
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
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_1);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(x_12);
x_15 = lean_expr_instantiate1(x_13, x_14);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
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
lean_inc_ref(x_4);
lean_inc(x_17);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_1, x_17, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_1 = x_19;
x_2 = x_17;
x_6 = x_20;
goto _start;
}
else
{
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
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
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_array_push(x_6, x_3);
x_11 = lean_array_push(x_7, x_4);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget(x_6, x_2);
x_13 = lean_expr_eqv(x_3, x_12);
lean_dec_ref(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fset(x_6, x_2, x_3);
x_18 = lean_array_fset(x_7, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_2, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_array_push(x_19, x_3);
x_24 = lean_array_push(x_20, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_fget(x_19, x_2);
x_27 = lean_expr_eqv(x_3, x_26);
lean_dec_ref(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_array_fset(x_19, x_2, x_3);
x_33 = lean_array_fset(x_20, x_2, x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__2___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget(x_2, x_4);
x_9 = lean_array_fget(x_3, x_4);
x_10 = l_Lean_Expr_hash(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_19 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__2___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = 5;
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___closed__1;
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_array_fget(x_6, x_11);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_6, x_11, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = lean_expr_eqv(x_4, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_15);
x_26 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_23, x_24, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_18 = x_27;
goto block_21;
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_18 = x_15;
goto block_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_expr_eqv(x_4, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_28, x_29, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_18 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
x_18 = x_33;
goto block_21;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_7);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_18 = x_15;
goto block_21;
}
else
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg(x_39, x_40, x_41, x_4, x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_18 = x_43;
goto block_21;
}
}
default: 
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_5);
x_18 = x_44;
goto block_21;
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fset(x_17, x_11, x_18);
lean_dec(x_11);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; size_t x_54; uint8_t x_55; 
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_5);
x_54 = 7;
x_55 = lean_usize_dec_le(x_54, x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_46);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_56);
x_47 = x_58;
goto block_53;
}
else
{
x_47 = x_55;
goto block_53;
}
block_53:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_46);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___closed__2;
x_52 = l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__2___redArg(x_3, x_48, x_49, x_50, x_51);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
return x_52;
}
else
{
return x_46;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; size_t x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__0___redArg(x_61, x_4, x_5);
x_70 = 7;
x_71 = lean_usize_dec_le(x_70, x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_62);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_72);
x_63 = x_74;
goto block_69;
}
else
{
x_63 = x_71;
goto block_69;
}
block_69:
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_62);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___closed__2;
x_68 = l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__2___redArg(x_3, x_64, x_65, x_66, x_67);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
return x_68;
}
else
{
return x_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Expr_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_1, x_3);
x_9 = lean_expr_eqv(x_4, x_8);
lean_dec_ref(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_2, x_3);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5_spec__5___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_box(2);
x_7 = 5;
x_8 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___closed__1;
x_9 = lean_usize_land(x_2, x_8);
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_array_get(x_6, x_5, x_10);
lean_dec(x_10);
lean_dec_ref(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_expr_eqv(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec_ref(x_11);
x_17 = lean_usize_shift_right(x_2, x_7);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_box(2);
x_22 = 5;
x_23 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___closed__1;
x_24 = lean_usize_land(x_2, x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_array_get(x_21, x_20, x_25);
lean_dec(x_25);
lean_dec_ref(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_expr_eqv(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec_ref(x_26);
x_33 = lean_usize_shift_right(x_2, x_22);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5_spec__5___redArg(x_36, x_37, x_38, x_3);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__0;
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
x_19 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__1;
x_20 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__2;
lean_inc_ref(x_14);
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
x_37 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__3;
x_38 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__4;
lean_inc_ref(x_32);
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
x_54 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__3;
x_55 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__4;
lean_inc_ref(x_50);
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
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_68, 2);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_68, 3);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_68, 4);
lean_inc_ref(x_72);
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
x_74 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__3;
x_75 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__4;
lean_inc_ref(x_69);
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
x_93 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__1;
x_94 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__2;
lean_inc_ref(x_89);
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
lean_inc_ref(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_103, 0);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_103, 2);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_103, 3);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_103, 4);
lean_inc_ref(x_108);
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
x_110 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__3;
x_111 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__4;
lean_inc_ref(x_105);
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
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_125, 2);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_125, 3);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_125, 4);
lean_inc_ref(x_129);
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
x_131 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__1;
x_132 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__2;
lean_inc_ref(x_126);
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
lean_inc_ref(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_142, 0);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_142, 2);
lean_inc_ref(x_145);
x_146 = lean_ctor_get(x_142, 3);
lean_inc_ref(x_146);
x_147 = lean_ctor_get(x_142, 4);
lean_inc_ref(x_147);
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
x_149 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__3;
x_150 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__4;
lean_inc_ref(x_144);
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
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information", 157, 157);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__5;
x_2 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__2;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__6;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg(x_2, x_8);
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
x_3 = lean_unsigned_to_nat(445u);
x_4 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__1;
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_38; 
x_38 = !lean_is_exclusive(x_5);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_39 = lean_ctor_get(x_5, 0);
x_40 = lean_ctor_get(x_5, 1);
x_41 = lean_ctor_get(x_5, 2);
x_42 = lean_ctor_get(x_5, 3);
x_43 = lean_ctor_get(x_5, 4);
x_44 = lean_ctor_get(x_5, 5);
x_45 = lean_ctor_get(x_5, 6);
x_46 = lean_ctor_get(x_5, 7);
x_47 = lean_ctor_get(x_5, 8);
x_48 = lean_ctor_get(x_5, 9);
x_49 = lean_ctor_get(x_5, 10);
x_50 = lean_ctor_get(x_5, 11);
x_51 = lean_ctor_get(x_5, 12);
x_52 = lean_nat_dec_eq(x_42, x_43);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_st_ref_get(x_2, x_7);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
x_57 = lean_ctor_get(x_55, 1);
lean_inc_ref(x_57);
lean_dec(x_55);
x_58 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5___redArg(x_57, x_1);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_free_object(x_53);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_42, x_59);
lean_dec(x_42);
lean_ctor_set(x_5, 3, x_60);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec_ref(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
x_62 = lean_st_ref_get(x_2, x_56);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec_ref(x_62);
x_65 = lean_ctor_get(x_63, 5);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___redArg(x_61, x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_61);
x_18 = x_67;
x_19 = x_2;
x_20 = x_64;
goto block_37;
}
else
{
lean_object* x_68; 
lean_dec(x_61);
x_68 = lean_box(0);
x_18 = x_68;
x_19 = x_2;
x_20 = x_64;
goto block_37;
}
}
case 4:
{
lean_object* x_69; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_69 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_2, x_3, x_4, x_5, x_6, x_56);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_18 = x_70;
x_19 = x_2;
x_20 = x_71;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_69;
}
}
case 5:
{
lean_object* x_72; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_72 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_2, x_3, x_4, x_5, x_6, x_56);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_18 = x_73;
x_19 = x_2;
x_20 = x_74;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_72;
}
}
case 6:
{
lean_object* x_75; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_75 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(x_1, x_2, x_3, x_4, x_5, x_6, x_56);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_18 = x_76;
x_19 = x_2;
x_20 = x_77;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_75;
}
}
case 8:
{
lean_object* x_78; lean_object* x_79; 
x_78 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda___closed__0;
lean_inc(x_2);
lean_inc_ref(x_1);
x_79 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(x_1, x_78, x_2, x_3, x_4, x_5, x_6, x_56);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
x_18 = x_80;
x_19 = x_2;
x_20 = x_81;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_79;
}
}
case 9:
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_82);
x_83 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(x_82, x_2, x_3, x_4, x_5, x_6, x_56);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec_ref(x_83);
x_18 = x_84;
x_19 = x_2;
x_20 = x_85;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_83;
}
}
case 10:
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_86);
lean_inc(x_2);
x_87 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(x_86, x_2, x_3, x_4, x_5, x_6, x_56);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec_ref(x_87);
x_18 = x_88;
x_19 = x_2;
x_20 = x_89;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_87;
}
}
case 11:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_1, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_1, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_92);
lean_inc(x_2);
x_93 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(x_90, x_91, x_92, x_2, x_3, x_4, x_5, x_6, x_56);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec_ref(x_93);
x_18 = x_94;
x_19 = x_2;
x_20 = x_95;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_93;
}
}
default: 
{
lean_object* x_96; lean_object* x_97; 
x_96 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__3;
lean_inc(x_2);
x_97 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8(x_96, x_2, x_3, x_4, x_5, x_6, x_56);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec_ref(x_97);
x_18 = x_98;
x_19 = x_2;
x_20 = x_99;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_97;
}
}
}
}
else
{
lean_object* x_100; 
lean_free_object(x_5);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_100 = lean_ctor_get(x_58, 0);
lean_inc(x_100);
lean_dec_ref(x_58);
lean_ctor_set(x_53, 0, x_100);
return x_53;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_53, 0);
x_102 = lean_ctor_get(x_53, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_53);
x_103 = lean_ctor_get(x_101, 1);
lean_inc_ref(x_103);
lean_dec(x_101);
x_104 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5___redArg(x_103, x_1);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_add(x_42, x_105);
lean_dec(x_42);
lean_ctor_set(x_5, 3, x_106);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec_ref(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_107 = lean_ctor_get(x_1, 0);
lean_inc(x_107);
x_108 = lean_st_ref_get(x_2, x_102);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec_ref(x_108);
x_111 = lean_ctor_get(x_109, 5);
lean_inc(x_111);
lean_dec(x_109);
x_112 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___redArg(x_107, x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_107);
x_18 = x_113;
x_19 = x_2;
x_20 = x_110;
goto block_37;
}
else
{
lean_object* x_114; 
lean_dec(x_107);
x_114 = lean_box(0);
x_18 = x_114;
x_19 = x_2;
x_20 = x_110;
goto block_37;
}
}
case 4:
{
lean_object* x_115; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_115 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_2, x_3, x_4, x_5, x_6, x_102);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec_ref(x_115);
x_18 = x_116;
x_19 = x_2;
x_20 = x_117;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_115;
}
}
case 5:
{
lean_object* x_118; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_118 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_2, x_3, x_4, x_5, x_6, x_102);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec_ref(x_118);
x_18 = x_119;
x_19 = x_2;
x_20 = x_120;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_118;
}
}
case 6:
{
lean_object* x_121; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_121 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(x_1, x_2, x_3, x_4, x_5, x_6, x_102);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec_ref(x_121);
x_18 = x_122;
x_19 = x_2;
x_20 = x_123;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_121;
}
}
case 8:
{
lean_object* x_124; lean_object* x_125; 
x_124 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda___closed__0;
lean_inc(x_2);
lean_inc_ref(x_1);
x_125 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(x_1, x_124, x_2, x_3, x_4, x_5, x_6, x_102);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec_ref(x_125);
x_18 = x_126;
x_19 = x_2;
x_20 = x_127;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_125;
}
}
case 9:
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_128);
x_129 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(x_128, x_2, x_3, x_4, x_5, x_6, x_102);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec_ref(x_129);
x_18 = x_130;
x_19 = x_2;
x_20 = x_131;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_129;
}
}
case 10:
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_132);
lean_inc(x_2);
x_133 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(x_132, x_2, x_3, x_4, x_5, x_6, x_102);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec_ref(x_133);
x_18 = x_134;
x_19 = x_2;
x_20 = x_135;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_133;
}
}
case 11:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_1, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_1, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_138);
lean_inc(x_2);
x_139 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(x_136, x_137, x_138, x_2, x_3, x_4, x_5, x_6, x_102);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec_ref(x_139);
x_18 = x_140;
x_19 = x_2;
x_20 = x_141;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_139;
}
}
default: 
{
lean_object* x_142; lean_object* x_143; 
x_142 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__3;
lean_inc(x_2);
x_143 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8(x_142, x_2, x_3, x_4, x_5, x_6, x_102);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec_ref(x_143);
x_18 = x_144;
x_19 = x_2;
x_20 = x_145;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_143;
}
}
}
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_free_object(x_5);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_146 = lean_ctor_get(x_104, 0);
lean_inc(x_146);
lean_dec_ref(x_104);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_102);
return x_147;
}
}
}
else
{
lean_object* x_148; 
lean_free_object(x_5);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_148 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg(x_44, x_7);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; uint8_t x_164; 
x_149 = lean_ctor_get(x_5, 0);
x_150 = lean_ctor_get(x_5, 1);
x_151 = lean_ctor_get(x_5, 2);
x_152 = lean_ctor_get(x_5, 3);
x_153 = lean_ctor_get(x_5, 4);
x_154 = lean_ctor_get(x_5, 5);
x_155 = lean_ctor_get(x_5, 6);
x_156 = lean_ctor_get(x_5, 7);
x_157 = lean_ctor_get(x_5, 8);
x_158 = lean_ctor_get(x_5, 9);
x_159 = lean_ctor_get(x_5, 10);
x_160 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_161 = lean_ctor_get(x_5, 11);
x_162 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_163 = lean_ctor_get(x_5, 12);
lean_inc(x_163);
lean_inc(x_161);
lean_inc(x_159);
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
lean_dec(x_5);
x_164 = lean_nat_dec_eq(x_152, x_153);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_165 = lean_st_ref_get(x_2, x_7);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_168 = x_165;
} else {
 lean_dec_ref(x_165);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_166, 1);
lean_inc_ref(x_169);
lean_dec(x_166);
x_170 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5___redArg(x_169, x_1);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_168);
x_171 = lean_unsigned_to_nat(1u);
x_172 = lean_nat_add(x_152, x_171);
lean_dec(x_152);
x_173 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_173, 0, x_149);
lean_ctor_set(x_173, 1, x_150);
lean_ctor_set(x_173, 2, x_151);
lean_ctor_set(x_173, 3, x_172);
lean_ctor_set(x_173, 4, x_153);
lean_ctor_set(x_173, 5, x_154);
lean_ctor_set(x_173, 6, x_155);
lean_ctor_set(x_173, 7, x_156);
lean_ctor_set(x_173, 8, x_157);
lean_ctor_set(x_173, 9, x_158);
lean_ctor_set(x_173, 10, x_159);
lean_ctor_set(x_173, 11, x_161);
lean_ctor_set(x_173, 12, x_163);
lean_ctor_set_uint8(x_173, sizeof(void*)*13, x_160);
lean_ctor_set_uint8(x_173, sizeof(void*)*13 + 1, x_162);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
lean_dec_ref(x_173);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_174 = lean_ctor_get(x_1, 0);
lean_inc(x_174);
x_175 = lean_st_ref_get(x_2, x_167);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec_ref(x_175);
x_178 = lean_ctor_get(x_176, 5);
lean_inc(x_178);
lean_dec(x_176);
x_179 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___redArg(x_174, x_178);
lean_dec(x_178);
if (x_179 == 0)
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_174);
x_18 = x_180;
x_19 = x_2;
x_20 = x_177;
goto block_37;
}
else
{
lean_object* x_181; 
lean_dec(x_174);
x_181 = lean_box(0);
x_18 = x_181;
x_19 = x_2;
x_20 = x_177;
goto block_37;
}
}
case 4:
{
lean_object* x_182; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_182 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_2, x_3, x_4, x_173, x_6, x_167);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec_ref(x_182);
x_18 = x_183;
x_19 = x_2;
x_20 = x_184;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_182;
}
}
case 5:
{
lean_object* x_185; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_185 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_2, x_3, x_4, x_173, x_6, x_167);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec_ref(x_185);
x_18 = x_186;
x_19 = x_2;
x_20 = x_187;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_185;
}
}
case 6:
{
lean_object* x_188; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_188 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(x_1, x_2, x_3, x_4, x_173, x_6, x_167);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec_ref(x_188);
x_18 = x_189;
x_19 = x_2;
x_20 = x_190;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_188;
}
}
case 8:
{
lean_object* x_191; lean_object* x_192; 
x_191 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda___closed__0;
lean_inc(x_2);
lean_inc_ref(x_1);
x_192 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(x_1, x_191, x_2, x_3, x_4, x_173, x_6, x_167);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec_ref(x_192);
x_18 = x_193;
x_19 = x_2;
x_20 = x_194;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_192;
}
}
case 9:
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_195);
x_196 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(x_195, x_2, x_3, x_4, x_173, x_6, x_167);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec_ref(x_196);
x_18 = x_197;
x_19 = x_2;
x_20 = x_198;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_196;
}
}
case 10:
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_199);
lean_inc(x_2);
x_200 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(x_199, x_2, x_3, x_4, x_173, x_6, x_167);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec_ref(x_200);
x_18 = x_201;
x_19 = x_2;
x_20 = x_202;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_inc_ref(x_205);
lean_inc(x_2);
x_206 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(x_203, x_204, x_205, x_2, x_3, x_4, x_173, x_6, x_167);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec_ref(x_206);
x_18 = x_207;
x_19 = x_2;
x_20 = x_208;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_206;
}
}
default: 
{
lean_object* x_209; lean_object* x_210; 
x_209 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__3;
lean_inc(x_2);
x_210 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8(x_209, x_2, x_3, x_4, x_173, x_6, x_167);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec_ref(x_210);
x_18 = x_211;
x_19 = x_2;
x_20 = x_212;
goto block_37;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_210;
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; 
lean_dec_ref(x_163);
lean_dec(x_161);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec_ref(x_150);
lean_dec_ref(x_149);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_213 = lean_ctor_get(x_170, 0);
lean_inc(x_213);
lean_dec_ref(x_170);
if (lean_is_scalar(x_168)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_168;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_167);
return x_214;
}
}
else
{
lean_object* x_215; 
lean_dec_ref(x_163);
lean_dec(x_161);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec_ref(x_150);
lean_dec_ref(x_149);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_215 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg(x_154, x_7);
return x_215;
}
}
block_17:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_st_ref_set(x_10, x_11, x_8);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
block_37:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_st_ref_take(x_19, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_22, sizeof(void*)*6);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec_ref(x_1);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec_ref(x_21);
x_8 = x_24;
x_9 = x_18;
x_10 = x_19;
x_11 = x_22;
goto block_17;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec_ref(x_21);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_18);
x_28 = l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___redArg(x_27, x_1, x_18);
lean_ctor_set(x_22, 1, x_28);
x_8 = x_25;
x_9 = x_18;
x_10 = x_19;
x_11 = x_22;
goto block_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
x_31 = lean_ctor_get(x_22, 2);
x_32 = lean_ctor_get(x_22, 3);
x_33 = lean_ctor_get(x_22, 4);
x_34 = lean_ctor_get(x_22, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
lean_inc(x_18);
x_35 = l_Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___redArg(x_30, x_1, x_18);
x_36 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_31);
lean_ctor_set(x_36, 3, x_32);
lean_ctor_set(x_36, 4, x_33);
lean_ctor_set(x_36, 5, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*6, x_23);
x_8 = x_25;
x_9 = x_18;
x_10 = x_19;
x_11 = x_36;
goto block_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_29; lean_object* x_30; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_st_ref_get(x_3, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_box(1);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_19 = lean_st_mk_ref(x_18, x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_22);
lean_dec(x_14);
x_23 = lean_expr_instantiate_rev(x_10, x_2);
lean_dec_ref(x_10);
x_24 = lean_expr_instantiate_rev(x_11, x_2);
lean_dec_ref(x_11);
x_58 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_59 = 0;
x_60 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_61 = lean_box(0);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_16);
lean_ctor_set(x_63, 2, x_22);
lean_ctor_set(x_63, 3, x_60);
lean_ctor_set(x_63, 4, x_61);
lean_ctor_set(x_63, 5, x_17);
lean_ctor_set(x_63, 6, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*7, x_59);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 1, x_59);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 2, x_59);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_20);
lean_inc_ref(x_23);
x_64 = l_Lean_Meta_isProp(x_23, x_63, x_20, x_6, x_7, x_21);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec_ref(x_64);
x_67 = lean_st_ref_get(x_20, x_66);
lean_dec(x_20);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = lean_unbox(x_65);
lean_dec(x_65);
x_29 = x_69;
x_30 = x_68;
goto block_57;
}
else
{
lean_dec(x_20);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
lean_dec_ref(x_64);
x_72 = lean_unbox(x_70);
lean_dec(x_70);
x_29 = x_72;
x_30 = x_71;
goto block_57;
}
else
{
uint8_t x_73; 
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_73 = !lean_is_exclusive(x_64);
if (x_73 == 0)
{
return x_64;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_64, 0);
x_75 = lean_ctor_get(x_64, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_64);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
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
lean_inc_ref(x_6);
lean_inc_ref(x_23);
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
lean_dec_ref(x_31);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_23);
x_35 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_23, x_3, x_6, x_7, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_24);
x_38 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_24, x_3, x_4, x_5, x_6, x_7, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(x_9, x_23, x_24, x_36, x_39, x_3, x_4, x_5, x_6, x_7, x_40);
lean_dec(x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
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
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_38;
}
}
else
{
uint8_t x_48; 
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_23);
lean_dec(x_9);
x_52 = lean_ctor_get(x_31, 1);
lean_inc(x_52);
lean_dec_ref(x_31);
x_25 = x_52;
goto block_28;
}
}
else
{
uint8_t x_53; 
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_23);
lean_dec(x_9);
x_25 = x_30;
goto block_28;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_78 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_77, x_3, x_4, x_5, x_6, x_7, x_8);
return x_78;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_ctor_get(x_5, 2);
x_12 = lean_ctor_get(x_5, 3);
x_13 = lean_ctor_get(x_5, 4);
x_14 = lean_ctor_get(x_5, 5);
x_15 = lean_ctor_get(x_5, 6);
x_16 = lean_ctor_get(x_5, 7);
x_17 = lean_ctor_get(x_5, 8);
x_18 = lean_ctor_get(x_5, 9);
x_19 = lean_ctor_get(x_5, 10);
x_20 = lean_ctor_get(x_5, 11);
x_21 = lean_ctor_get(x_5, 12);
x_22 = lean_nat_dec_eq(x_12, x_13);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_58; lean_object* x_59; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_24 = lean_st_ref_get(x_2, x_7);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_box(1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_30 = lean_st_mk_ref(x_29, x_26);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_34);
lean_dec(x_25);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_12, x_35);
lean_dec(x_12);
lean_ctor_set(x_5, 3, x_36);
x_86 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_87 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_88 = lean_box(0);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_27);
lean_ctor_set(x_90, 2, x_34);
lean_ctor_set(x_90, 3, x_87);
lean_ctor_set(x_90, 4, x_88);
lean_ctor_set(x_90, 5, x_28);
lean_ctor_set(x_90, 6, x_89);
lean_ctor_set_uint8(x_90, sizeof(void*)*7, x_22);
lean_ctor_set_uint8(x_90, sizeof(void*)*7 + 1, x_22);
lean_ctor_set_uint8(x_90, sizeof(void*)*7 + 2, x_22);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_31);
lean_inc_ref(x_1);
x_91 = lean_infer_type(x_1, x_90, x_31, x_5, x_6, x_32);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec_ref(x_91);
x_94 = lean_st_ref_get(x_31, x_93);
lean_dec(x_31);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec_ref(x_94);
x_58 = x_92;
x_59 = x_95;
goto block_85;
}
else
{
lean_dec(x_31);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_91, 1);
lean_inc(x_97);
lean_dec_ref(x_91);
x_58 = x_96;
x_59 = x_97;
goto block_85;
}
else
{
uint8_t x_98; 
lean_dec_ref(x_5);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_98 = !lean_is_exclusive(x_91);
if (x_98 == 0)
{
return x_91;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_91, 0);
x_100 = lean_ctor_get(x_91, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_91);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
block_57:
{
if (x_38 == 0)
{
lean_object* x_40; 
lean_dec(x_33);
lean_inc(x_6);
lean_inc_ref(x_5);
x_40 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_37, x_2, x_5, x_6, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec_ref(x_40);
x_44 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(x_1, x_2, x_3, x_4, x_5, x_6, x_43);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec_ref(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_40, 0);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set(x_40, 0, x_47);
return x_40;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_dec(x_40);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec_ref(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_51 = !lean_is_exclusive(x_40);
if (x_51 == 0)
{
return x_40;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_40, 0);
x_53 = lean_ctor_get(x_40, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_40);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec_ref(x_37);
lean_dec_ref(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_55 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_33;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_39);
return x_56;
}
}
block_85:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = lean_st_ref_get(x_2, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = lean_st_mk_ref(x_29, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = lean_ctor_get(x_61, 0);
lean_inc_ref(x_66);
lean_dec(x_61);
x_67 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_68 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_69 = lean_box(0);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_27);
lean_ctor_set(x_71, 2, x_66);
lean_ctor_set(x_71, 3, x_68);
lean_ctor_set(x_71, 4, x_69);
lean_ctor_set(x_71, 5, x_28);
lean_ctor_set(x_71, 6, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*7, x_22);
lean_ctor_set_uint8(x_71, sizeof(void*)*7 + 1, x_22);
lean_ctor_set_uint8(x_71, sizeof(void*)*7 + 2, x_22);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_64);
lean_inc_ref(x_58);
x_72 = l_Lean_Meta_isProp(x_58, x_71, x_64, x_5, x_6, x_65);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_75 = lean_st_ref_get(x_64, x_74);
lean_dec(x_64);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = lean_unbox(x_73);
lean_dec(x_73);
x_37 = x_58;
x_38 = x_77;
x_39 = x_76;
goto block_57;
}
else
{
lean_dec(x_64);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_dec_ref(x_72);
x_80 = lean_unbox(x_78);
lean_dec(x_78);
x_37 = x_58;
x_38 = x_80;
x_39 = x_79;
goto block_57;
}
else
{
uint8_t x_81; 
lean_dec_ref(x_58);
lean_dec_ref(x_5);
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_81 = !lean_is_exclusive(x_72);
if (x_81 == 0)
{
return x_72;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_72, 0);
x_83 = lean_ctor_get(x_72, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_72);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_free_object(x_5);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_7);
return x_103;
}
}
else
{
lean_object* x_104; 
lean_free_object(x_5);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_104 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg(x_14, x_7);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; uint8_t x_120; 
x_105 = lean_ctor_get(x_5, 0);
x_106 = lean_ctor_get(x_5, 1);
x_107 = lean_ctor_get(x_5, 2);
x_108 = lean_ctor_get(x_5, 3);
x_109 = lean_ctor_get(x_5, 4);
x_110 = lean_ctor_get(x_5, 5);
x_111 = lean_ctor_get(x_5, 6);
x_112 = lean_ctor_get(x_5, 7);
x_113 = lean_ctor_get(x_5, 8);
x_114 = lean_ctor_get(x_5, 9);
x_115 = lean_ctor_get(x_5, 10);
x_116 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_117 = lean_ctor_get(x_5, 11);
x_118 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_119 = lean_ctor_get(x_5, 12);
lean_inc(x_119);
lean_inc(x_117);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_5);
x_120 = lean_nat_dec_eq(x_108, x_109);
if (x_120 == 0)
{
uint8_t x_121; 
x_121 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof(x_1);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_155; lean_object* x_156; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_122 = lean_st_ref_get(x_2, x_7);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec_ref(x_122);
x_125 = lean_box(1);
x_126 = lean_unsigned_to_nat(0u);
x_127 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_128 = lean_st_mk_ref(x_127, x_124);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_123, 0);
lean_inc_ref(x_132);
lean_dec(x_123);
x_133 = lean_unsigned_to_nat(1u);
x_134 = lean_nat_add(x_108, x_133);
lean_dec(x_108);
x_135 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_135, 0, x_105);
lean_ctor_set(x_135, 1, x_106);
lean_ctor_set(x_135, 2, x_107);
lean_ctor_set(x_135, 3, x_134);
lean_ctor_set(x_135, 4, x_109);
lean_ctor_set(x_135, 5, x_110);
lean_ctor_set(x_135, 6, x_111);
lean_ctor_set(x_135, 7, x_112);
lean_ctor_set(x_135, 8, x_113);
lean_ctor_set(x_135, 9, x_114);
lean_ctor_set(x_135, 10, x_115);
lean_ctor_set(x_135, 11, x_117);
lean_ctor_set(x_135, 12, x_119);
lean_ctor_set_uint8(x_135, sizeof(void*)*13, x_116);
lean_ctor_set_uint8(x_135, sizeof(void*)*13 + 1, x_118);
x_183 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_184 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_185 = lean_box(0);
x_186 = lean_box(0);
x_187 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_187, 0, x_183);
lean_ctor_set(x_187, 1, x_125);
lean_ctor_set(x_187, 2, x_132);
lean_ctor_set(x_187, 3, x_184);
lean_ctor_set(x_187, 4, x_185);
lean_ctor_set(x_187, 5, x_126);
lean_ctor_set(x_187, 6, x_186);
lean_ctor_set_uint8(x_187, sizeof(void*)*7, x_120);
lean_ctor_set_uint8(x_187, sizeof(void*)*7 + 1, x_120);
lean_ctor_set_uint8(x_187, sizeof(void*)*7 + 2, x_120);
lean_inc(x_6);
lean_inc_ref(x_135);
lean_inc(x_129);
lean_inc_ref(x_1);
x_188 = lean_infer_type(x_1, x_187, x_129, x_135, x_6, x_130);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec_ref(x_188);
x_191 = lean_st_ref_get(x_129, x_190);
lean_dec(x_129);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec_ref(x_191);
x_155 = x_189;
x_156 = x_192;
goto block_182;
}
else
{
lean_dec(x_129);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_188, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_188, 1);
lean_inc(x_194);
lean_dec_ref(x_188);
x_155 = x_193;
x_156 = x_194;
goto block_182;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec_ref(x_135);
lean_dec(x_131);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_195 = lean_ctor_get(x_188, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_188, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_197 = x_188;
} else {
 lean_dec_ref(x_188);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
block_154:
{
if (x_137 == 0)
{
lean_object* x_139; 
lean_dec(x_131);
lean_inc(x_6);
lean_inc_ref(x_135);
x_139 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_136, x_2, x_135, x_6, x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec_ref(x_139);
x_143 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(x_1, x_2, x_3, x_4, x_135, x_6, x_142);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec_ref(x_135);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_144 = lean_ctor_get(x_139, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_145 = x_139;
} else {
 lean_dec_ref(x_139);
 x_145 = lean_box(0);
}
x_146 = lean_box(0);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_144);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec_ref(x_135);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_148 = lean_ctor_get(x_139, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_139, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_150 = x_139;
} else {
 lean_dec_ref(x_139);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec_ref(x_136);
lean_dec_ref(x_135);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_152 = lean_box(0);
if (lean_is_scalar(x_131)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_131;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_138);
return x_153;
}
}
block_182:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_157 = lean_st_ref_get(x_2, x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec_ref(x_157);
x_160 = lean_st_mk_ref(x_127, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec_ref(x_160);
x_163 = lean_ctor_get(x_158, 0);
lean_inc_ref(x_163);
lean_dec(x_158);
x_164 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_165 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_166 = lean_box(0);
x_167 = lean_box(0);
x_168 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_168, 0, x_164);
lean_ctor_set(x_168, 1, x_125);
lean_ctor_set(x_168, 2, x_163);
lean_ctor_set(x_168, 3, x_165);
lean_ctor_set(x_168, 4, x_166);
lean_ctor_set(x_168, 5, x_126);
lean_ctor_set(x_168, 6, x_167);
lean_ctor_set_uint8(x_168, sizeof(void*)*7, x_120);
lean_ctor_set_uint8(x_168, sizeof(void*)*7 + 1, x_120);
lean_ctor_set_uint8(x_168, sizeof(void*)*7 + 2, x_120);
lean_inc(x_6);
lean_inc_ref(x_135);
lean_inc(x_161);
lean_inc_ref(x_155);
x_169 = l_Lean_Meta_isProp(x_155, x_168, x_161, x_135, x_6, x_162);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec_ref(x_169);
x_172 = lean_st_ref_get(x_161, x_171);
lean_dec(x_161);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec_ref(x_172);
x_174 = lean_unbox(x_170);
lean_dec(x_170);
x_136 = x_155;
x_137 = x_174;
x_138 = x_173;
goto block_154;
}
else
{
lean_dec(x_161);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_175 = lean_ctor_get(x_169, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_169, 1);
lean_inc(x_176);
lean_dec_ref(x_169);
x_177 = lean_unbox(x_175);
lean_dec(x_175);
x_136 = x_155;
x_137 = x_177;
x_138 = x_176;
goto block_154;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec_ref(x_155);
lean_dec_ref(x_135);
lean_dec(x_131);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_178 = lean_ctor_get(x_169, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_169, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_180 = x_169;
} else {
 lean_dec_ref(x_169);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
}
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_dec_ref(x_119);
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_105);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_199 = lean_box(0);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_7);
return x_200;
}
}
else
{
lean_object* x_201; 
lean_dec_ref(x_119);
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_105);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_201 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg(x_110, x_7);
return x_201;
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
lean_inc_ref(x_5);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_12, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toCode(x_14, x_2, x_3, x_4, x_5, x_6, x_15);
lean_dec(x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__1;
x_20 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_11, x_17, x_19, x_3, x_4, x_5, x_6, x_18);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
lean_inc_ref(x_1);
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
lean_dec_ref(x_12);
x_34 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_31, x_2, x_3, x_4, x_5, x_6, x_10);
return x_34;
}
else
{
lean_dec_ref(x_31);
goto block_30;
}
}
else
{
lean_dec_ref(x_31);
lean_dec_ref(x_11);
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
lean_dec_ref(x_13);
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
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_13);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15;
x_16 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_4);
return x_16;
}
default: 
{
uint8_t x_17; 
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_12, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_unsigned_to_nat(0u);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_inc_ref(x_7);
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
lean_inc_ref(x_11);
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
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
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
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
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
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_16;
}
case 1:
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_array_size(x_2);
x_21 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_22 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0(x_20, x_21, x_2, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15;
x_27 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_25, x_26, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_4);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
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
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
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
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_16;
}
case 1:
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_array_size(x_2);
x_21 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_22 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0(x_20, x_21, x_2, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15;
x_27 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_25, x_26, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_4);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
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
x_1 = lean_mk_string_unchecked("rec", 3, 3);
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
x_1 = lean_mk_string_unchecked("recOn", 5, 5);
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
x_1 = lean_mk_string_unchecked("HEq", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("And", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Iff", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__14;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__16;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Empty", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__18;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lcUnreachable", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__20;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22() {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_14 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_14);
lean_dec(x_9);
x_15 = l_Lean_Expr_getAppFn(x_1);
x_16 = l_Lean_Compiler_CSimp_replaceConstants(x_14, x_15);
lean_dec_ref(x_15);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2;
x_19 = lean_name_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4;
x_21 = lean_name_eq(x_17, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6;
x_23 = lean_name_eq(x_17, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8;
x_25 = lean_name_eq(x_17, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2;
x_27 = lean_name_eq(x_17, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10;
x_29 = lean_name_eq(x_17, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11;
x_31 = lean_name_eq(x_17, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13;
x_33 = lean_name_eq(x_17, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15;
x_35 = lean_name_eq(x_17, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17;
x_37 = lean_name_eq(x_17, x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__19;
x_39 = lean_name_eq(x_17, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__21;
x_41 = lean_name_eq(x_17, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_17);
x_42 = l_Lean_Compiler_LCNF_getCasesInfo_x3f(x_17, x_5, x_6, x_10);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
lean_inc_ref(x_5);
lean_inc(x_17);
x_45 = l_Lean_Compiler_LCNF_getCtorArity_x3f(x_17, x_5, x_6, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = lean_st_ref_get(x_6, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc_ref(x_51);
lean_dec(x_49);
lean_inc(x_17);
x_52 = lean_is_no_confusion(x_51, x_17);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__1___redArg(x_17, x_6, x_50);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22;
x_57 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_57);
x_58 = lean_mk_array(x_57, x_56);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_sub(x_57, x_59);
lean_dec(x_57);
x_61 = l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__2(x_1, x_58, x_60, x_2, x_3, x_4, x_5, x_6, x_55);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_53, 1);
lean_inc(x_62);
lean_dec_ref(x_53);
x_63 = lean_ctor_get(x_54, 0);
lean_inc(x_63);
lean_dec_ref(x_54);
x_64 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(x_63, x_1, x_2, x_3, x_4, x_5, x_6, x_62);
lean_dec(x_63);
return x_64;
}
}
else
{
lean_object* x_65; 
lean_dec(x_17);
x_65 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion(x_1, x_2, x_3, x_4, x_5, x_6, x_50);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_17);
x_66 = lean_ctor_get(x_45, 1);
lean_inc(x_66);
lean_dec_ref(x_45);
x_67 = lean_ctor_get(x_46, 0);
lean_inc(x_67);
lean_dec_ref(x_46);
x_68 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(x_67, x_1, x_2, x_3, x_4, x_5, x_6, x_66);
lean_dec(x_67);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_69 = !lean_is_exclusive(x_45);
if (x_69 == 0)
{
return x_45;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_45, 0);
x_71 = lean_ctor_get(x_45, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_45);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_17);
x_73 = lean_ctor_get(x_42, 1);
lean_inc(x_73);
lean_dec_ref(x_42);
x_74 = lean_ctor_get(x_43, 0);
lean_inc(x_74);
lean_dec_ref(x_43);
x_75 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(x_74, x_1, x_2, x_3, x_4, x_5, x_6, x_73);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_76 = !lean_is_exclusive(x_42);
if (x_76 == 0)
{
return x_42;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_42, 0);
x_78 = lean_ctor_get(x_42, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_42);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; 
lean_dec(x_17);
x_80 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_80;
}
}
else
{
lean_object* x_81; 
lean_dec(x_17);
x_81 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_81;
}
}
else
{
lean_object* x_82; 
lean_dec(x_17);
x_82 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_82;
}
}
else
{
lean_dec(x_17);
goto block_13;
}
}
else
{
lean_dec(x_17);
goto block_13;
}
}
else
{
lean_object* x_83; 
lean_dec(x_17);
x_83 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_17);
x_84 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_84;
}
}
else
{
lean_object* x_85; 
lean_dec(x_17);
x_85 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_85;
}
}
else
{
lean_object* x_86; 
lean_dec(x_17);
x_86 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_86;
}
}
else
{
lean_object* x_87; 
lean_dec(x_17);
x_87 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_17);
x_88 = lean_unsigned_to_nat(3u);
x_89 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(x_88, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_89;
}
}
else
{
lean_object* x_90; 
lean_dec(x_17);
x_90 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec_ref(x_16);
x_91 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22;
x_92 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_92);
x_93 = lean_mk_array(x_92, x_91);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_sub(x_92, x_94);
lean_dec(x_92);
x_96 = l_Lean_Expr_withAppAux___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__3(x_1, x_93, x_95, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_95);
return x_96;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_10);
return x_12;
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
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_93 = lean_st_ref_get(x_2, x_7);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec_ref(x_93);
x_96 = lean_box(1);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_99 = lean_st_mk_ref(x_98, x_95);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec_ref(x_99);
x_102 = lean_ctor_get(x_94, 0);
lean_inc_ref(x_102);
lean_dec(x_94);
x_103 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_104 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_105 = lean_box(0);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_107, 1, x_96);
lean_ctor_set(x_107, 2, x_102);
lean_ctor_set(x_107, 3, x_104);
lean_ctor_set(x_107, 4, x_105);
lean_ctor_set(x_107, 5, x_97);
lean_ctor_set(x_107, 6, x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*7, x_61);
lean_ctor_set_uint8(x_107, sizeof(void*)*7 + 1, x_61);
lean_ctor_set_uint8(x_107, sizeof(void*)*7 + 2, x_61);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_100);
lean_inc_ref(x_1);
x_108 = lean_infer_type(x_1, x_107, x_100, x_5, x_6, x_101);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec_ref(x_108);
x_111 = lean_st_ref_get(x_100, x_110);
lean_dec(x_100);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec_ref(x_111);
x_62 = x_109;
x_63 = x_112;
goto block_92;
}
else
{
lean_dec(x_100);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_108, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
lean_dec_ref(x_108);
x_62 = x_113;
x_63 = x_114;
goto block_92;
}
else
{
uint8_t x_115; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_115 = !lean_is_exclusive(x_108);
if (x_115 == 0)
{
return x_108;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_108, 0);
x_117 = lean_ctor_get(x_108, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_108);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_7);
return x_120;
}
block_60:
{
if (x_9 == 0)
{
lean_object* x_11; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_8);
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
lean_dec_ref(x_8);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec_ref(x_11);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(x_1, x_2, x_3, x_4, x_5, x_6, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec_ref(x_11);
lean_inc(x_6);
lean_inc_ref(x_5);
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
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_10);
return x_59;
}
}
block_92:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_64 = lean_st_ref_get(x_2, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec_ref(x_64);
x_67 = lean_box(1);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_70 = lean_st_mk_ref(x_69, x_66);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec_ref(x_70);
x_73 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_73);
lean_dec(x_65);
x_74 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_75 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_76 = lean_box(0);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set(x_78, 1, x_67);
lean_ctor_set(x_78, 2, x_73);
lean_ctor_set(x_78, 3, x_75);
lean_ctor_set(x_78, 4, x_76);
lean_ctor_set(x_78, 5, x_68);
lean_ctor_set(x_78, 6, x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*7, x_61);
lean_ctor_set_uint8(x_78, sizeof(void*)*7 + 1, x_61);
lean_ctor_set_uint8(x_78, sizeof(void*)*7 + 2, x_61);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_71);
lean_inc_ref(x_62);
x_79 = l_Lean_Meta_isProp(x_62, x_78, x_71, x_5, x_6, x_72);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
x_82 = lean_st_ref_get(x_71, x_81);
lean_dec(x_71);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = lean_unbox(x_80);
lean_dec(x_80);
x_8 = x_62;
x_9 = x_84;
x_10 = x_83;
goto block_60;
}
else
{
lean_dec(x_71);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_79, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec_ref(x_79);
x_87 = lean_unbox(x_85);
lean_dec(x_85);
x_8 = x_62;
x_9 = x_87;
x_10 = x_86;
goto block_60;
}
else
{
uint8_t x_88; 
lean_dec_ref(x_62);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_88 = !lean_is_exclusive(x_79);
if (x_88 == 0)
{
return x_79;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_79, 0);
x_90 = lean_ctor_get(x_79, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_79);
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
x_2 = lean_unsigned_to_nat(61u);
x_3 = lean_unsigned_to_nat(488u);
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
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_12);
lean_dec(x_10);
lean_inc_ref(x_12);
x_13 = l_Lean_Compiler_CSimp_replaceConstants(x_12, x_1);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_array_size(x_2);
x_17 = 0;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_18 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__0(x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_31; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
lean_inc(x_14);
x_31 = l_Lean_hasNeverExtractAttribute_visit(x_12, x_14);
if (x_31 == 0)
{
x_21 = x_3;
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
x_26 = x_20;
goto block_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_st_ref_take(x_3, x_20);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_36 = 0;
lean_ctor_set_uint8(x_33, sizeof(void*)*6, x_36);
x_37 = lean_st_ref_set(x_3, x_33, x_34);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec_ref(x_37);
x_21 = x_3;
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
x_26 = x_38;
goto block_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
x_41 = lean_ctor_get(x_33, 2);
x_42 = lean_ctor_get(x_33, 3);
x_43 = lean_ctor_get(x_33, 4);
x_44 = lean_ctor_get(x_33, 5);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
x_45 = 0;
x_46 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_40);
lean_ctor_set(x_46, 2, x_41);
lean_ctor_set(x_46, 3, x_42);
lean_ctor_set(x_46, 4, x_43);
lean_ctor_set(x_46, 5, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*6, x_45);
x_47 = lean_st_ref_set(x_3, x_46, x_34);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
x_21 = x_3;
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
x_26 = x_48;
goto block_30;
}
}
block_30:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_15);
lean_ctor_set(x_27, 2, x_19);
x_28 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15;
x_29 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_27, x_28, x_21, x_22, x_23, x_24, x_25, x_26);
lean_dec(x_21);
return x_29;
}
}
else
{
uint8_t x_49; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_18);
if (x_49 == 0)
{
return x_18;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_18, 0);
x_51 = lean_ctor_get(x_18, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_18);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_2);
x_53 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1;
x_54 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8(x_53, x_3, x_4, x_5, x_6, x_7, x_11);
return x_54;
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_unknownIdentifierMessageTag;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___closed__0;
x_10 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__4;
x_3 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("A private declaration `", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` exists but is not accessible in the current context.", 54, 54);
return x_1;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_17; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_13);
lean_dec(x_11);
x_17 = l_Lean_Name_isAnonymous(x_2);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = lean_ctor_get_uint8(x_13, sizeof(void*)*8);
if (x_18 == 0)
{
lean_dec_ref(x_13);
lean_free_object(x_9);
lean_dec(x_2);
goto block_16;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Environment_setExporting(x_13, x_17);
lean_inc(x_2);
lean_inc_ref(x_19);
x_20 = l_Lean_Environment_contains(x_19, x_2, x_18);
if (x_20 == 0)
{
lean_dec_ref(x_19);
lean_free_object(x_9);
lean_dec(x_2);
goto block_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_21 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__7;
x_22 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1;
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
x_25 = l_Lean_MessageData_ofConstName(x_2, x_17);
lean_ctor_set_tag(x_9, 3);
lean_ctor_set(x_9, 1, x_25);
lean_ctor_set(x_9, 0, x_24);
x_26 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
x_28 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__5;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_MessageData_note(x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(0);
x_33 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(x_31, x_32, x_3, x_4, x_5, x_6, x_7, x_12);
return x_33;
}
}
}
else
{
lean_dec_ref(x_13);
lean_free_object(x_9);
lean_dec(x_2);
goto block_16;
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_12);
return x_15;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_40; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_36 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_36);
lean_dec(x_34);
x_40 = l_Lean_Name_isAnonymous(x_2);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = lean_ctor_get_uint8(x_36, sizeof(void*)*8);
if (x_41 == 0)
{
lean_dec_ref(x_36);
lean_dec(x_2);
goto block_39;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_Environment_setExporting(x_36, x_40);
lean_inc(x_2);
lean_inc_ref(x_42);
x_43 = l_Lean_Environment_contains(x_42, x_2, x_41);
if (x_43 == 0)
{
lean_dec_ref(x_42);
lean_dec(x_2);
goto block_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_44 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__7;
x_45 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1;
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_46);
x_48 = l_Lean_MessageData_ofConstName(x_2, x_40);
x_49 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__5;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_MessageData_note(x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_box(0);
x_57 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(x_55, x_56, x_3, x_4, x_5, x_6, x_7, x_35);
return x_57;
}
}
}
else
{
lean_dec_ref(x_36);
lean_dec(x_2);
goto block_39;
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
x_38 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(x_1, x_37, x_3, x_4, x_5, x_6, x_7, x_35);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_inc_ref(x_15);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_dec(x_18);
x_19 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec_ref(x_17);
x_20 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__7;
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
lean_dec_ref(x_22);
x_24 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__7;
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
lean_inc_ref(x_29);
lean_dec(x_10);
x_30 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_30);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_31 = x_27;
} else {
 lean_dec_ref(x_27);
 x_31 = lean_box(0);
}
x_32 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_30);
lean_dec_ref(x_30);
x_33 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__7;
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
lean_inc_ref(x_43);
lean_dec(x_37);
x_44 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_44);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_45 = x_40;
} else {
 lean_dec_ref(x_40);
 x_45 = lean_box(0);
}
x_46 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_44);
lean_dec_ref(x_44);
x_47 = l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__7;
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___redArg(x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 5);
x_11 = l_Lean_replaceRef(x_1, x_10);
lean_dec(x_10);
lean_ctor_set(x_6, 5, x_11);
x_12 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___redArg(x_2, x_5, x_6, x_7, x_8);
lean_dec_ref(x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_ctor_get(x_6, 3);
x_17 = lean_ctor_get(x_6, 4);
x_18 = lean_ctor_get(x_6, 5);
x_19 = lean_ctor_get(x_6, 6);
x_20 = lean_ctor_get(x_6, 7);
x_21 = lean_ctor_get(x_6, 8);
x_22 = lean_ctor_get(x_6, 9);
x_23 = lean_ctor_get(x_6, 10);
x_24 = lean_ctor_get_uint8(x_6, sizeof(void*)*13);
x_25 = lean_ctor_get(x_6, 11);
x_26 = lean_ctor_get_uint8(x_6, sizeof(void*)*13 + 1);
x_27 = lean_ctor_get(x_6, 12);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_28 = l_Lean_replaceRef(x_1, x_18);
lean_dec(x_18);
x_29 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_14);
lean_ctor_set(x_29, 2, x_15);
lean_ctor_set(x_29, 3, x_16);
lean_ctor_set(x_29, 4, x_17);
lean_ctor_set(x_29, 5, x_28);
lean_ctor_set(x_29, 6, x_19);
lean_ctor_set(x_29, 7, x_20);
lean_ctor_set(x_29, 8, x_21);
lean_ctor_set(x_29, 9, x_22);
lean_ctor_set(x_29, 10, x_23);
lean_ctor_set(x_29, 11, x_25);
lean_ctor_set(x_29, 12, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*13, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*13 + 1, x_26);
x_30 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___redArg(x_2, x_5, x_29, x_7, x_8);
lean_dec_ref(x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1___redArg(x_1, x_11, x_4, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unknown constant `", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__1;
x_10 = 0;
lean_inc(x_2);
x_11 = l_Lean_MessageData_ofConstName(x_2, x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__3;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 5);
lean_inc(x_8);
x_9 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_12);
lean_dec(x_10);
x_13 = 0;
lean_inc(x_1);
x_14 = l_Lean_Environment_find_x3f(x_12, x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_free_object(x_8);
x_15 = l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec_ref(x_5);
lean_dec(x_1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_19);
lean_dec(x_17);
x_20 = 0;
lean_inc(x_1);
x_21 = l_Lean_Environment_find_x3f(x_19, x_1, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_18);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_5);
lean_dec(x_1);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
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
x_3 = lean_unsigned_to_nat(681u);
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
x_12 = l_Lean_Compiler_LCNF_isRuntimeBuiltinType(x_11);
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
lean_dec_ref(x_13);
lean_inc_ref(x_6);
x_16 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0(x_14, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Lean_Core_instantiateValueLevelParams(x_17, x_15, x_6, x_7, x_18);
lean_dec(x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22;
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_13);
lean_dec_ref(x_2);
x_38 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1;
x_39 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8(x_38, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_45 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22;
lean_inc(x_40);
x_46 = lean_mk_array(x_40, x_45);
x_47 = lean_nat_sub(x_40, x_41);
lean_dec(x_40);
x_48 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_46, x_47);
x_49 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(x_44, x_48, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_44);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_nat_sub(x_42, x_40);
lean_dec(x_40);
lean_dec(x_42);
lean_inc(x_7);
lean_inc_ref(x_6);
x_51 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_2, x_50, x_3, x_6, x_7, x_8);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_52, x_3, x_4, x_5, x_6, x_7, x_53);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
x_12 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg(x_1, x_2, x_6, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; uint8_t x_23; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_22 = lean_array_get_size(x_3);
x_23 = lean_nat_dec_le(x_4, x_5);
if (x_23 == 0)
{
lean_dec(x_5);
x_15 = x_4;
x_16 = x_22;
goto block_21;
}
else
{
lean_dec(x_4);
x_15 = x_5;
x_16 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = l_Array_toSubarray___redArg(x_3, x_15, x_16);
x_18 = l_Array_ofSubarray___redArg(x_17);
lean_dec_ref(x_17);
x_19 = l_Lean_mkAppN(x_13, x_18);
lean_dec_ref(x_18);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_19, x_6, x_7, x_8, x_9, x_10, x_14);
return x_20;
}
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_27; lean_object* x_28; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_113; lean_object* x_114; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_145 = lean_st_ref_get(x_10, x_15);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec_ref(x_145);
x_148 = lean_box(1);
x_149 = lean_unsigned_to_nat(0u);
x_150 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_151 = lean_st_mk_ref(x_150, x_147);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec_ref(x_151);
x_154 = lean_ctor_get(x_146, 0);
lean_inc_ref(x_154);
lean_dec(x_146);
x_155 = lean_nat_add(x_7, x_8);
lean_inc_ref(x_5);
x_156 = lean_array_get(x_5, x_6, x_155);
lean_dec(x_155);
x_157 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_158 = 0;
x_159 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_160 = lean_box(0);
x_161 = lean_box(0);
x_162 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_162, 0, x_157);
lean_ctor_set(x_162, 1, x_148);
lean_ctor_set(x_162, 2, x_154);
lean_ctor_set(x_162, 3, x_159);
lean_ctor_set(x_162, 4, x_160);
lean_ctor_set(x_162, 5, x_149);
lean_ctor_set(x_162, 6, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*7, x_158);
lean_ctor_set_uint8(x_162, sizeof(void*)*7 + 1, x_158);
lean_ctor_set_uint8(x_162, sizeof(void*)*7 + 2, x_158);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_152);
x_163 = lean_whnf(x_156, x_162, x_152, x_13, x_14, x_153);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec_ref(x_163);
x_166 = lean_st_ref_get(x_152, x_165);
lean_dec(x_152);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec_ref(x_166);
x_113 = x_164;
x_114 = x_167;
goto block_144;
}
else
{
lean_dec(x_152);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_163, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_163, 1);
lean_inc(x_169);
lean_dec_ref(x_163);
x_113 = x_168;
x_114 = x_169;
goto block_144;
}
else
{
uint8_t x_170; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_170 = !lean_is_exclusive(x_163);
if (x_170 == 0)
{
return x_163;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_163, 0);
x_172 = lean_ctor_get(x_163, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_163);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
block_26:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__1;
x_21 = l_Lean_MessageData_ofName(x_1);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__3;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___redArg(x_24, x_16, x_17, x_18, x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
return x_25;
}
block_37:
{
lean_object* x_29; 
lean_inc(x_14);
lean_inc_ref(x_13);
x_29 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_27, x_10, x_13, x_14, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_30, x_10, x_11, x_12, x_13, x_14, x_31);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
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
block_80:
{
if (lean_obj_tag(x_40) == 0)
{
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_16 = x_12;
x_17 = x_13;
x_18 = x_14;
x_19 = x_44;
goto block_26;
}
else
{
if (lean_obj_tag(x_43) == 0)
{
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_16 = x_12;
x_17 = x_13;
x_18 = x_14;
x_19 = x_44;
goto block_26;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_1);
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
lean_dec_ref(x_40);
x_46 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
lean_dec_ref(x_43);
x_48 = lean_ctor_get(x_47, 0);
lean_inc_ref(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get(x_45, 4);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_ctor_get(x_46, 0);
lean_inc(x_50);
lean_dec_ref(x_46);
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
lean_dec_ref(x_48);
x_52 = lean_name_eq(x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_49);
lean_dec(x_38);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_53 = lean_st_ref_get(x_10, x_44);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = lean_st_mk_ref(x_42, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec_ref(x_56);
x_59 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_59);
lean_dec(x_54);
x_60 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_61 = lean_mk_empty_array_with_capacity(x_39);
x_62 = lean_box(0);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_41);
lean_ctor_set(x_64, 2, x_59);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_62);
lean_ctor_set(x_64, 5, x_39);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*7, x_52);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 1, x_52);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 2, x_52);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_57);
x_65 = lean_infer_type(x_2, x_64, x_57, x_13, x_14, x_58);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec_ref(x_65);
x_68 = lean_st_ref_get(x_57, x_67);
lean_dec(x_57);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec_ref(x_68);
x_27 = x_66;
x_28 = x_69;
goto block_37;
}
else
{
lean_dec(x_57);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
lean_dec_ref(x_65);
x_27 = x_70;
x_28 = x_71;
goto block_37;
}
else
{
uint8_t x_72; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
x_72 = !lean_is_exclusive(x_65);
if (x_72 == 0)
{
return x_65;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_65, 0);
x_74 = lean_ctor_get(x_65, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_65);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_39);
x_76 = lean_nat_add(x_3, x_4);
x_77 = lean_array_get(x_5, x_6, x_3);
lean_inc(x_76);
x_78 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__0), 11, 5);
lean_closure_set(x_78, 0, x_77);
lean_closure_set(x_78, 1, x_49);
lean_closure_set(x_78, 2, x_6);
lean_closure_set(x_78, 3, x_76);
lean_closure_set(x_78, 4, x_38);
x_79 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_2, x_76, x_78, x_10, x_11, x_12, x_13, x_14, x_44);
lean_dec(x_76);
return x_79;
}
}
}
}
block_112:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_88 = lean_st_ref_get(x_10, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec_ref(x_88);
lean_inc_ref(x_85);
x_91 = lean_st_mk_ref(x_85, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec_ref(x_91);
x_94 = lean_ctor_get(x_89, 0);
lean_inc_ref(x_94);
lean_dec(x_89);
x_95 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_96 = 0;
x_97 = lean_mk_empty_array_with_capacity(x_82);
x_98 = lean_box(0);
x_99 = lean_box(0);
lean_inc(x_82);
lean_inc(x_83);
x_100 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_83);
lean_ctor_set(x_100, 2, x_94);
lean_ctor_set(x_100, 3, x_97);
lean_ctor_set(x_100, 4, x_98);
lean_ctor_set(x_100, 5, x_82);
lean_ctor_set(x_100, 6, x_99);
lean_ctor_set_uint8(x_100, sizeof(void*)*7, x_96);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 1, x_96);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 2, x_96);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_92);
x_101 = l_Lean_Meta_isConstructorApp_x3f(x_84, x_100, x_92, x_13, x_14, x_93);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec_ref(x_101);
x_104 = lean_st_ref_get(x_92, x_103);
lean_dec(x_92);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec_ref(x_104);
x_38 = x_81;
x_39 = x_82;
x_40 = x_86;
x_41 = x_83;
x_42 = x_85;
x_43 = x_102;
x_44 = x_105;
goto block_80;
}
else
{
lean_dec(x_92);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_101, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
lean_dec_ref(x_101);
x_38 = x_81;
x_39 = x_82;
x_40 = x_86;
x_41 = x_83;
x_42 = x_85;
x_43 = x_106;
x_44 = x_107;
goto block_80;
}
else
{
uint8_t x_108; 
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_101);
if (x_108 == 0)
{
return x_101;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_101, 0);
x_110 = lean_ctor_get(x_101, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_101);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
block_144:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_115 = lean_st_ref_get(x_10, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec_ref(x_115);
x_118 = lean_box(1);
x_119 = lean_unsigned_to_nat(0u);
x_120 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_121 = lean_st_mk_ref(x_120, x_117);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec_ref(x_121);
x_124 = lean_ctor_get(x_116, 0);
lean_inc_ref(x_124);
lean_dec(x_116);
x_125 = l_Lean_Expr_toCtorIfLit(x_9);
x_126 = l_Lean_Expr_toCtorIfLit(x_113);
x_127 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_128 = 0;
x_129 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_130 = lean_box(0);
x_131 = lean_box(0);
x_132 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_118);
lean_ctor_set(x_132, 2, x_124);
lean_ctor_set(x_132, 3, x_129);
lean_ctor_set(x_132, 4, x_130);
lean_ctor_set(x_132, 5, x_119);
lean_ctor_set(x_132, 6, x_131);
lean_ctor_set_uint8(x_132, sizeof(void*)*7, x_128);
lean_ctor_set_uint8(x_132, sizeof(void*)*7 + 1, x_128);
lean_ctor_set_uint8(x_132, sizeof(void*)*7 + 2, x_128);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_122);
x_133 = l_Lean_Meta_isConstructorApp_x3f(x_125, x_132, x_122, x_13, x_14, x_123);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec_ref(x_133);
x_136 = lean_st_ref_get(x_122, x_135);
lean_dec(x_122);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec_ref(x_136);
x_81 = x_119;
x_82 = x_119;
x_83 = x_118;
x_84 = x_126;
x_85 = x_120;
x_86 = x_134;
x_87 = x_137;
goto block_112;
}
else
{
lean_dec(x_122);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_133, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_133, 1);
lean_inc(x_139);
lean_dec_ref(x_133);
x_81 = x_119;
x_82 = x_119;
x_83 = x_118;
x_84 = x_126;
x_85 = x_120;
x_86 = x_138;
x_87 = x_139;
goto block_112;
}
else
{
uint8_t x_140; 
lean_dec_ref(x_126);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_133);
if (x_140 == 0)
{
return x_133;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_133, 0);
x_142 = lean_ctor_get(x_133, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_133);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_box(1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_15 = lean_st_mk_ref(x_14, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_18);
lean_dec(x_10);
x_19 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_20 = 0;
x_21 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_22 = lean_box(0);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_12);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set(x_24, 5, x_13);
lean_ctor_set(x_24, 6, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*7, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*7 + 1, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*7 + 2, x_20);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_16);
x_25 = lean_whnf(x_1, x_24, x_16, x_6, x_7, x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_st_ref_get(x_16, x_27);
lean_dec(x_16);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_apply_7(x_2, x_26, x_3, x_4, x_5, x_6, x_7, x_29);
return x_30;
}
else
{
lean_dec(x_16);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec_ref(x_25);
x_33 = lean_apply_7(x_2, x_31, x_3, x_4, x_5, x_6, x_7, x_32);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
return x_25;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_25);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
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
x_3 = lean_unsigned_to_nat(639u);
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
x_3 = lean_unsigned_to_nat(637u);
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
lean_dec_ref(x_8);
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
lean_inc_ref(x_5);
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
lean_inc_ref(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
lean_dec_ref(x_14);
x_18 = lean_nat_add(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_18, x_19);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_add(x_20, x_21);
x_23 = lean_nat_add(x_22, x_19);
lean_dec(x_22);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22;
x_25 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_25);
x_26 = lean_mk_array(x_25, x_24);
x_27 = lean_nat_sub(x_25, x_19);
lean_dec(x_25);
lean_inc_ref(x_1);
x_28 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_26, x_27);
lean_inc_ref(x_28);
lean_inc(x_23);
lean_inc_ref(x_1);
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
lean_dec_ref(x_28);
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
lean_dec_ref(x_1);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_dec_ref(x_12);
x_34 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1;
x_35 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8(x_34, x_2, x_3, x_4, x_5, x_6, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_42 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__2;
x_43 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8(x_42, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_dec_ref(x_1);
x_12 = lean_apply_6(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_3);
x_13 = lean_nat_sub(x_2, x_10);
lean_dec(x_10);
lean_inc(x_8);
lean_inc_ref(x_7);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_1, x_13, x_4, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_15, x_4, x_5, x_6, x_7, x_8, x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_4, 1);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_12, 1, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_11);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
lean_dec(x_4);
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_27 = x_15;
} else {
 lean_dec_ref(x_15);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_12, 1, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_12);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_11);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_4);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_12, 1);
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
x_39 = lean_ctor_get(x_14, 0);
x_40 = lean_ctor_get(x_14, 1);
x_41 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 2);
lean_inc(x_43);
x_44 = lean_nat_dec_lt(x_42, x_43);
if (x_44 == 0)
{
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_39);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
lean_ctor_set(x_12, 0, x_40);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
else
{
uint8_t x_45; 
lean_free_object(x_14);
x_45 = !lean_is_exclusive(x_33);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_33, 2);
lean_dec(x_46);
x_47 = lean_ctor_get(x_33, 1);
lean_dec(x_47);
x_48 = lean_ctor_get(x_33, 0);
lean_dec(x_48);
x_49 = lean_array_fget(x_41, x_42);
lean_inc_ref(x_1);
x_50 = lean_array_get(x_1, x_2, x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_51 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_39, x_49, x_50, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_42, x_57);
lean_dec(x_42);
lean_ctor_set(x_33, 1, x_58);
x_59 = l_Lean_Compiler_LCNF_joinTypes(x_55, x_38);
x_60 = lean_array_push(x_37, x_56);
lean_ctor_set(x_32, 1, x_59);
lean_ctor_set(x_32, 0, x_60);
lean_ctor_set(x_12, 0, x_40);
x_61 = lean_nat_add(x_5, x_57);
lean_dec(x_5);
x_62 = lean_nat_dec_lt(x_61, x_3);
if (x_62 == 0)
{
lean_dec(x_61);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
lean_ctor_set(x_51, 0, x_4);
return x_51;
}
else
{
lean_free_object(x_51);
x_5 = x_61;
x_11 = x_54;
goto _start;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_64 = lean_ctor_get(x_51, 0);
x_65 = lean_ctor_get(x_51, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_51);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_add(x_42, x_68);
lean_dec(x_42);
lean_ctor_set(x_33, 1, x_69);
x_70 = l_Lean_Compiler_LCNF_joinTypes(x_66, x_38);
x_71 = lean_array_push(x_37, x_67);
lean_ctor_set(x_32, 1, x_70);
lean_ctor_set(x_32, 0, x_71);
lean_ctor_set(x_12, 0, x_40);
x_72 = lean_nat_add(x_5, x_68);
lean_dec(x_5);
x_73 = lean_nat_dec_lt(x_72, x_3);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_72);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_4);
lean_ctor_set(x_74, 1, x_65);
return x_74;
}
else
{
x_5 = x_72;
x_11 = x_65;
goto _start;
}
}
}
else
{
uint8_t x_76; 
lean_free_object(x_33);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_free_object(x_32);
lean_dec(x_38);
lean_dec(x_37);
lean_free_object(x_4);
lean_free_object(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_76 = !lean_is_exclusive(x_51);
if (x_76 == 0)
{
return x_51;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_51, 0);
x_78 = lean_ctor_get(x_51, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_51);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_33);
x_80 = lean_array_fget(x_41, x_42);
lean_inc_ref(x_1);
x_81 = lean_array_get(x_1, x_2, x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_82 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_39, x_80, x_81, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_dec(x_83);
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_add(x_42, x_88);
lean_dec(x_42);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_41);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_43);
x_91 = l_Lean_Compiler_LCNF_joinTypes(x_86, x_38);
x_92 = lean_array_push(x_37, x_87);
lean_ctor_set(x_32, 1, x_91);
lean_ctor_set(x_32, 0, x_92);
lean_ctor_set(x_12, 0, x_40);
lean_ctor_set(x_4, 0, x_90);
x_93 = lean_nat_add(x_5, x_88);
lean_dec(x_5);
x_94 = lean_nat_dec_lt(x_93, x_3);
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_93);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
if (lean_is_scalar(x_85)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_85;
}
lean_ctor_set(x_95, 0, x_4);
lean_ctor_set(x_95, 1, x_84);
return x_95;
}
else
{
lean_dec(x_85);
x_5 = x_93;
x_11 = x_84;
goto _start;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_free_object(x_32);
lean_dec(x_38);
lean_dec(x_37);
lean_free_object(x_4);
lean_free_object(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_97 = lean_ctor_get(x_82, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_82, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_99 = x_82;
} else {
 lean_dec_ref(x_82);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_101 = lean_ctor_get(x_32, 0);
x_102 = lean_ctor_get(x_32, 1);
x_103 = lean_ctor_get(x_14, 0);
x_104 = lean_ctor_get(x_14, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_14);
x_105 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_33, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_33, 2);
lean_inc(x_107);
x_108 = lean_nat_dec_lt(x_106, x_107);
if (x_108 == 0)
{
lean_object* x_109; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec_ref(x_105);
lean_dec(x_103);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
lean_ctor_set(x_12, 0, x_104);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_4);
lean_ctor_set(x_109, 1, x_11);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 x_110 = x_33;
} else {
 lean_dec_ref(x_33);
 x_110 = lean_box(0);
}
x_111 = lean_array_fget(x_105, x_106);
lean_inc_ref(x_1);
x_112 = lean_array_get(x_1, x_2, x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_113 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_103, x_111, x_112, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
lean_dec(x_114);
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_nat_add(x_106, x_119);
lean_dec(x_106);
if (lean_is_scalar(x_110)) {
 x_121 = lean_alloc_ctor(0, 3, 0);
} else {
 x_121 = x_110;
}
lean_ctor_set(x_121, 0, x_105);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set(x_121, 2, x_107);
x_122 = l_Lean_Compiler_LCNF_joinTypes(x_117, x_102);
x_123 = lean_array_push(x_101, x_118);
lean_ctor_set(x_32, 1, x_122);
lean_ctor_set(x_32, 0, x_123);
lean_ctor_set(x_12, 0, x_104);
lean_ctor_set(x_4, 0, x_121);
x_124 = lean_nat_add(x_5, x_119);
lean_dec(x_5);
x_125 = lean_nat_dec_lt(x_124, x_3);
if (x_125 == 0)
{
lean_object* x_126; 
lean_dec(x_124);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
if (lean_is_scalar(x_116)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_116;
}
lean_ctor_set(x_126, 0, x_4);
lean_ctor_set(x_126, 1, x_115);
return x_126;
}
else
{
lean_dec(x_116);
x_5 = x_124;
x_11 = x_115;
goto _start;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_110);
lean_dec(x_107);
lean_dec(x_106);
lean_dec_ref(x_105);
lean_dec(x_104);
lean_free_object(x_32);
lean_dec(x_102);
lean_dec(x_101);
lean_free_object(x_4);
lean_free_object(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_128 = lean_ctor_get(x_113, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_113, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_130 = x_113;
} else {
 lean_dec_ref(x_113);
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
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_132 = lean_ctor_get(x_32, 0);
x_133 = lean_ctor_get(x_32, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_32);
x_134 = lean_ctor_get(x_14, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_14, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_136 = x_14;
} else {
 lean_dec_ref(x_14);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_137);
x_138 = lean_ctor_get(x_33, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_33, 2);
lean_inc(x_139);
x_140 = lean_nat_dec_lt(x_138, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_134);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_132);
lean_ctor_set(x_141, 1, x_133);
lean_ctor_set(x_12, 1, x_141);
lean_ctor_set(x_12, 0, x_135);
if (lean_is_scalar(x_136)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_136;
 lean_ctor_set_tag(x_142, 0);
}
lean_ctor_set(x_142, 0, x_4);
lean_ctor_set(x_142, 1, x_11);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_136);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 x_143 = x_33;
} else {
 lean_dec_ref(x_33);
 x_143 = lean_box(0);
}
x_144 = lean_array_fget(x_137, x_138);
lean_inc_ref(x_1);
x_145 = lean_array_get(x_1, x_2, x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_146 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_134, x_144, x_145, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
x_150 = lean_ctor_get(x_147, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_147, 1);
lean_inc(x_151);
lean_dec(x_147);
x_152 = lean_unsigned_to_nat(1u);
x_153 = lean_nat_add(x_138, x_152);
lean_dec(x_138);
if (lean_is_scalar(x_143)) {
 x_154 = lean_alloc_ctor(0, 3, 0);
} else {
 x_154 = x_143;
}
lean_ctor_set(x_154, 0, x_137);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set(x_154, 2, x_139);
x_155 = l_Lean_Compiler_LCNF_joinTypes(x_150, x_133);
x_156 = lean_array_push(x_132, x_151);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
lean_ctor_set(x_12, 1, x_157);
lean_ctor_set(x_12, 0, x_135);
lean_ctor_set(x_4, 0, x_154);
x_158 = lean_nat_add(x_5, x_152);
lean_dec(x_5);
x_159 = lean_nat_dec_lt(x_158, x_3);
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec(x_158);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
if (lean_is_scalar(x_149)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_149;
}
lean_ctor_set(x_160, 0, x_4);
lean_ctor_set(x_160, 1, x_148);
return x_160;
}
else
{
lean_dec(x_149);
x_5 = x_158;
x_11 = x_148;
goto _start;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_143);
lean_dec(x_139);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_132);
lean_free_object(x_4);
lean_free_object(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_162 = lean_ctor_get(x_146, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_146, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_164 = x_146;
} else {
 lean_dec_ref(x_146);
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
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_166 = lean_ctor_get(x_12, 1);
x_167 = lean_ctor_get(x_4, 0);
lean_inc(x_167);
lean_dec(x_4);
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_170 = x_166;
} else {
 lean_dec_ref(x_166);
 x_170 = lean_box(0);
}
x_171 = lean_ctor_get(x_14, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_14, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_173 = x_14;
} else {
 lean_dec_ref(x_14);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_167, 0);
lean_inc_ref(x_174);
x_175 = lean_ctor_get(x_167, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_167, 2);
lean_inc(x_176);
x_177 = lean_nat_dec_lt(x_175, x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_176);
lean_dec(x_175);
lean_dec_ref(x_174);
lean_dec(x_171);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_is_scalar(x_170)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_170;
}
lean_ctor_set(x_178, 0, x_168);
lean_ctor_set(x_178, 1, x_169);
lean_ctor_set(x_12, 1, x_178);
lean_ctor_set(x_12, 0, x_172);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_167);
lean_ctor_set(x_179, 1, x_12);
if (lean_is_scalar(x_173)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_173;
 lean_ctor_set_tag(x_180, 0);
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_11);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_173);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 lean_ctor_release(x_167, 2);
 x_181 = x_167;
} else {
 lean_dec_ref(x_167);
 x_181 = lean_box(0);
}
x_182 = lean_array_fget(x_174, x_175);
lean_inc_ref(x_1);
x_183 = lean_array_get(x_1, x_2, x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_184 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_171, x_182, x_183, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_185, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_185, 1);
lean_inc(x_189);
lean_dec(x_185);
x_190 = lean_unsigned_to_nat(1u);
x_191 = lean_nat_add(x_175, x_190);
lean_dec(x_175);
if (lean_is_scalar(x_181)) {
 x_192 = lean_alloc_ctor(0, 3, 0);
} else {
 x_192 = x_181;
}
lean_ctor_set(x_192, 0, x_174);
lean_ctor_set(x_192, 1, x_191);
lean_ctor_set(x_192, 2, x_176);
x_193 = l_Lean_Compiler_LCNF_joinTypes(x_188, x_169);
x_194 = lean_array_push(x_168, x_189);
if (lean_is_scalar(x_170)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_170;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
lean_ctor_set(x_12, 1, x_195);
lean_ctor_set(x_12, 0, x_172);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_192);
lean_ctor_set(x_196, 1, x_12);
x_197 = lean_nat_add(x_5, x_190);
lean_dec(x_5);
x_198 = lean_nat_dec_lt(x_197, x_3);
if (x_198 == 0)
{
lean_object* x_199; 
lean_dec(x_197);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
if (lean_is_scalar(x_187)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_187;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_186);
return x_199;
}
else
{
lean_dec(x_187);
x_4 = x_196;
x_5 = x_197;
x_11 = x_186;
goto _start;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_181);
lean_dec(x_176);
lean_dec(x_175);
lean_dec_ref(x_174);
lean_dec(x_172);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_free_object(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_201 = lean_ctor_get(x_184, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_184, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_203 = x_184;
} else {
 lean_dec_ref(x_184);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
}
}
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_12, 1);
x_206 = lean_ctor_get(x_12, 0);
lean_inc(x_205);
lean_inc(x_206);
lean_dec(x_12);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_207 = lean_ctor_get(x_4, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_208 = x_4;
} else {
 lean_dec_ref(x_4);
 x_208 = lean_box(0);
}
x_209 = lean_ctor_get(x_205, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_205, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_211 = x_205;
} else {
 lean_dec_ref(x_205);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_206);
lean_ctor_set(x_213, 1, x_212);
if (lean_is_scalar(x_208)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_208;
}
lean_ctor_set(x_214, 0, x_207);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_11);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_216 = lean_ctor_get(x_4, 0);
lean_inc(x_216);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_217 = x_4;
} else {
 lean_dec_ref(x_4);
 x_217 = lean_box(0);
}
x_218 = lean_ctor_get(x_205, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_205, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_220 = x_205;
} else {
 lean_dec_ref(x_205);
 x_220 = lean_box(0);
}
x_221 = lean_ctor_get(x_206, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_206, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_223 = x_206;
} else {
 lean_dec_ref(x_206);
 x_223 = lean_box(0);
}
x_224 = lean_ctor_get(x_216, 0);
lean_inc_ref(x_224);
x_225 = lean_ctor_get(x_216, 1);
lean_inc(x_225);
x_226 = lean_ctor_get(x_216, 2);
lean_inc(x_226);
x_227 = lean_nat_dec_lt(x_225, x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_226);
lean_dec(x_225);
lean_dec_ref(x_224);
lean_dec(x_221);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
if (lean_is_scalar(x_220)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_220;
}
lean_ctor_set(x_228, 0, x_218);
lean_ctor_set(x_228, 1, x_219);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_222);
lean_ctor_set(x_229, 1, x_228);
if (lean_is_scalar(x_217)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_217;
}
lean_ctor_set(x_230, 0, x_216);
lean_ctor_set(x_230, 1, x_229);
if (lean_is_scalar(x_223)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_223;
 lean_ctor_set_tag(x_231, 0);
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_11);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_223);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 lean_ctor_release(x_216, 2);
 x_232 = x_216;
} else {
 lean_dec_ref(x_216);
 x_232 = lean_box(0);
}
x_233 = lean_array_fget(x_224, x_225);
lean_inc_ref(x_1);
x_234 = lean_array_get(x_1, x_2, x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_235 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_221, x_233, x_234, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_238 = x_235;
} else {
 lean_dec_ref(x_235);
 x_238 = lean_box(0);
}
x_239 = lean_ctor_get(x_236, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_236, 1);
lean_inc(x_240);
lean_dec(x_236);
x_241 = lean_unsigned_to_nat(1u);
x_242 = lean_nat_add(x_225, x_241);
lean_dec(x_225);
if (lean_is_scalar(x_232)) {
 x_243 = lean_alloc_ctor(0, 3, 0);
} else {
 x_243 = x_232;
}
lean_ctor_set(x_243, 0, x_224);
lean_ctor_set(x_243, 1, x_242);
lean_ctor_set(x_243, 2, x_226);
x_244 = l_Lean_Compiler_LCNF_joinTypes(x_239, x_219);
x_245 = lean_array_push(x_218, x_240);
if (lean_is_scalar(x_220)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_220;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_244);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_222);
lean_ctor_set(x_247, 1, x_246);
if (lean_is_scalar(x_217)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_217;
}
lean_ctor_set(x_248, 0, x_243);
lean_ctor_set(x_248, 1, x_247);
x_249 = lean_nat_add(x_5, x_241);
lean_dec(x_5);
x_250 = lean_nat_dec_lt(x_249, x_3);
if (x_250 == 0)
{
lean_object* x_251; 
lean_dec(x_249);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
if (lean_is_scalar(x_238)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_238;
}
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_237);
return x_251;
}
else
{
lean_dec(x_238);
x_4 = x_248;
x_5 = x_249;
x_11 = x_237;
goto _start;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_232);
lean_dec(x_226);
lean_dec(x_225);
lean_dec_ref(x_224);
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
x_253 = lean_ctor_get(x_235, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_235, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_255 = x_235;
} else {
 lean_dec_ref(x_235);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
x_19 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(x_1, x_2, x_7, x_9, x_10, x_13, x_14, x_15, x_16, x_17, x_18);
return x_19;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitCases", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__2;
x_2 = lean_unsigned_to_nat(57u);
x_3 = lean_unsigned_to_nat(565u);
x_4 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__1;
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc_ref(x_12);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_8, x_9, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_Lean_Compiler_LCNF_CasesInfo_numAlts(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0;
if (lean_obj_tag(x_7) == 0)
{
x_105 = x_7;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_7, 0);
lean_inc(x_135);
lean_dec(x_7);
x_105 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = l_Lean_instInhabitedExpr;
x_107 = lean_array_get(x_106, x_2, x_6);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
x_108 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_107, x_9, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec_ref(x_108);
lean_inc_ref(x_12);
lean_inc(x_105);
x_111 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0(x_105, x_9, x_10, x_11, x_12, x_13, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 5)
{
if (lean_obj_tag(x_109) == 1)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec_ref(x_111);
x_114 = lean_ctor_get(x_112, 0);
lean_inc_ref(x_114);
lean_dec_ref(x_112);
x_115 = lean_ctor_get(x_109, 0);
lean_inc(x_115);
lean_dec_ref(x_109);
x_51 = x_114;
x_52 = x_106;
x_53 = x_105;
x_54 = x_104;
x_55 = x_16;
x_56 = x_115;
x_57 = x_9;
x_58 = x_10;
x_59 = x_11;
x_60 = x_12;
x_61 = x_13;
x_62 = x_113;
goto block_103;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_109);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
lean_dec_ref(x_111);
x_117 = lean_ctor_get(x_112, 0);
lean_inc_ref(x_117);
lean_dec_ref(x_112);
x_118 = lean_box(1);
x_119 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15;
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_120 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_118, x_119, x_9, x_10, x_11, x_12, x_13, x_116);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec_ref(x_120);
x_51 = x_117;
x_52 = x_106;
x_53 = x_105;
x_54 = x_104;
x_55 = x_16;
x_56 = x_121;
x_57 = x_9;
x_58 = x_10;
x_59 = x_11;
x_60 = x_12;
x_61 = x_13;
x_62 = x_122;
goto block_103;
}
else
{
uint8_t x_123; 
lean_dec_ref(x_117);
lean_dec(x_105);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_123 = !lean_is_exclusive(x_120);
if (x_123 == 0)
{
return x_120;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_120, 0);
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_120);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_112);
lean_dec(x_109);
lean_dec(x_105);
lean_dec(x_16);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_127 = lean_ctor_get(x_111, 1);
lean_inc(x_127);
lean_dec_ref(x_111);
x_128 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__2;
x_129 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8(x_128, x_9, x_10, x_11, x_12, x_13, x_127);
return x_129;
}
}
else
{
uint8_t x_130; 
lean_dec(x_109);
lean_dec(x_105);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_130 = !lean_is_exclusive(x_111);
if (x_130 == 0)
{
return x_111;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_111, 0);
x_132 = lean_ctor_get(x_111, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_111);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
lean_dec(x_105);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_108;
}
}
}
else
{
lean_object* x_136; 
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_136 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_16, x_9, x_10, x_11, x_12, x_13, x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
return x_136;
}
block_50:
{
lean_object* x_31; uint8_t x_32; 
lean_inc_ref(x_29);
x_31 = l_Lean_Compiler_LCNF_mkAuxParam(x_29, x_20, x_22, x_23, x_26, x_27, x_30);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_35, 2, x_24);
lean_ctor_set(x_35, 3, x_28);
lean_inc(x_33);
lean_ctor_set_tag(x_31, 3);
lean_ctor_set(x_31, 1, x_35);
x_36 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_31, x_21, x_34);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_39, x_2, x_3, x_21, x_22, x_23, x_26, x_27, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_ctor_get(x_31, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_31);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_25);
lean_ctor_set(x_43, 1, x_29);
lean_ctor_set(x_43, 2, x_24);
lean_ctor_set(x_43, 3, x_28);
lean_inc(x_41);
x_44 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_44, x_21, x_42);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_ctor_get(x_41, 0);
lean_inc(x_47);
lean_dec(x_41);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_48, x_2, x_3, x_21, x_22, x_23, x_26, x_27, x_46);
return x_49;
}
}
block_103:
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_4);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_4, 0);
x_65 = lean_ctor_get(x_4, 1);
x_66 = lean_nat_dec_lt(x_64, x_65);
if (x_66 == 0)
{
lean_free_object(x_4);
lean_dec(x_65);
lean_dec(x_64);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_5);
x_21 = x_57;
x_22 = x_58;
x_23 = x_59;
x_24 = x_56;
x_25 = x_53;
x_26 = x_60;
x_27 = x_61;
x_28 = x_54;
x_29 = x_55;
x_30 = x_62;
goto block_50;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_51, 4);
lean_inc(x_67);
lean_dec_ref(x_51);
x_68 = lean_array_get_size(x_5);
x_69 = l_Array_toSubarray___redArg(x_5, x_19, x_68);
lean_ctor_set(x_4, 1, x_55);
lean_ctor_set(x_4, 0, x_54);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_4);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
lean_inc(x_61);
lean_inc_ref(x_60);
lean_inc(x_59);
lean_inc_ref(x_58);
lean_inc(x_57);
x_72 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(x_52, x_2, x_65, x_71, x_64, x_57, x_58, x_59, x_60, x_61, x_62);
lean_dec(x_65);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec_ref(x_72);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_21 = x_57;
x_22 = x_58;
x_23 = x_59;
x_24 = x_56;
x_25 = x_53;
x_26 = x_60;
x_27 = x_61;
x_28 = x_77;
x_29 = x_78;
x_30 = x_76;
goto block_50;
}
else
{
uint8_t x_79; 
lean_dec(x_61);
lean_dec_ref(x_60);
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_3);
x_79 = !lean_is_exclusive(x_72);
if (x_79 == 0)
{
return x_72;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_72, 0);
x_81 = lean_ctor_get(x_72, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_72);
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
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_4, 0);
x_84 = lean_ctor_get(x_4, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_4);
x_85 = lean_nat_dec_lt(x_83, x_84);
if (x_85 == 0)
{
lean_dec(x_84);
lean_dec(x_83);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_5);
x_21 = x_57;
x_22 = x_58;
x_23 = x_59;
x_24 = x_56;
x_25 = x_53;
x_26 = x_60;
x_27 = x_61;
x_28 = x_54;
x_29 = x_55;
x_30 = x_62;
goto block_50;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_86 = lean_ctor_get(x_51, 4);
lean_inc(x_86);
lean_dec_ref(x_51);
x_87 = lean_array_get_size(x_5);
x_88 = l_Array_toSubarray___redArg(x_5, x_19, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_54);
lean_ctor_set(x_89, 1, x_55);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_61);
lean_inc_ref(x_60);
lean_inc(x_59);
lean_inc_ref(x_58);
lean_inc(x_57);
x_92 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(x_52, x_2, x_84, x_91, x_83, x_57, x_58, x_59, x_60, x_61, x_62);
lean_dec(x_84);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec_ref(x_92);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_21 = x_57;
x_22 = x_58;
x_23 = x_59;
x_24 = x_56;
x_25 = x_53;
x_26 = x_60;
x_27 = x_61;
x_28 = x_97;
x_29 = x_98;
x_30 = x_96;
goto block_50;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_61);
lean_dec_ref(x_60);
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_3);
x_99 = lean_ctor_get(x_92, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_92, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_101 = x_92;
} else {
 lean_dec_ref(x_92);
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
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_137 = !lean_is_exclusive(x_15);
if (x_137 == 0)
{
return x_15;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_15, 0);
x_139 = lean_ctor_get(x_15, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_15);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_box(1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_15 = lean_st_mk_ref(x_14, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_18);
lean_dec(x_10);
x_19 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_20 = 0;
x_21 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_22 = lean_box(0);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_12);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set(x_24, 5, x_13);
lean_ctor_set(x_24, 6, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*7, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*7 + 1, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*7 + 2, x_20);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_16);
x_25 = lean_infer_type(x_1, x_24, x_16, x_6, x_7, x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_st_ref_get(x_16, x_27);
lean_dec(x_16);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_apply_7(x_2, x_26, x_3, x_4, x_5, x_6, x_7, x_29);
return x_30;
}
else
{
lean_dec(x_16);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec_ref(x_25);
x_33 = lean_apply_7(x_2, x_31, x_3, x_4, x_5, x_6, x_7, x_32);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
return x_25;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_25);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_13);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22;
x_15 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_15);
x_16 = lean_mk_array(x_15, x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_15, x_17);
lean_dec(x_15);
lean_inc_ref(x_2);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_16, x_18);
x_20 = l_Lean_Expr_getAppFn(x_2);
lean_inc(x_10);
lean_inc_ref(x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___boxed), 14, 7);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_19);
lean_closure_set(x_21, 2, x_10);
lean_closure_set(x_21, 3, x_12);
lean_closure_set(x_21, 4, x_13);
lean_closure_set(x_21, 5, x_11);
lean_closure_set(x_21, 6, x_9);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get_size(x_19);
x_32 = lean_nat_dec_le(x_10, x_31);
if (x_32 == 0)
{
x_22 = x_30;
x_23 = x_31;
goto block_29;
}
else
{
lean_dec(x_31);
lean_inc(x_10);
x_22 = x_30;
x_23 = x_10;
goto block_29;
}
block_29:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = l_Array_toSubarray___redArg(x_19, x_22, x_23);
x_25 = l_Array_ofSubarray___redArg(x_24);
lean_dec_ref(x_24);
x_26 = l_Lean_mkAppN(x_20, x_25);
lean_dec_ref(x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1), 8, 2);
lean_closure_set(x_27, 0, x_26);
lean_closure_set(x_27, 1, x_21);
x_28 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_2, x_10, x_27, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_fget(x_1, x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_12 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_11, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_array_push(x_3, x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_4, x_17);
lean_dec(x_4);
x_19 = lean_nat_dec_lt(x_18, x_2);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_free_object(x_12);
x_3 = x_16;
x_4 = x_18;
x_10 = x_15;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_array_push(x_3, x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_26 = lean_nat_dec_lt(x_25, x_2);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_25);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
else
{
x_3 = x_23;
x_4 = x_25;
x_10 = x_22;
goto _start;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
return x_12;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_12);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg(x_1, x_6, x_8, x_9, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec_ref(x_1);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___closed__0;
x_21 = lean_nat_dec_lt(x_3, x_10);
if (x_21 == 0)
{
lean_dec(x_10);
lean_dec(x_3);
x_14 = x_20;
x_15 = x_9;
goto block_19;
}
else
{
lean_object* x_22; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_22 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg(x_2, x_10, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_14 = x_23;
x_15 = x_24;
goto block_19;
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
block_19:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15;
x_18 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_4);
return x_18;
}
}
default: 
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_9);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_9);
return x_31;
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_14 = l_Lean_Compiler_LCNF_inferType(x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc(x_8);
lean_inc_ref(x_7);
x_17 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_15, x_4, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_37; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_unsigned_to_nat(0u);
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
lean_dec_ref(x_38);
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
lean_dec_ref(x_45);
lean_inc(x_6);
x_22 = x_4;
x_23 = x_6;
x_24 = x_46;
goto block_36;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_47 = lean_ctor_get(x_39, 0);
x_48 = lean_ctor_get(x_39, 1);
x_49 = lean_ctor_get_uint8(x_39, sizeof(void*)*6);
x_50 = lean_ctor_get(x_39, 2);
x_51 = lean_ctor_get(x_39, 3);
x_52 = lean_ctor_get(x_39, 4);
x_53 = lean_ctor_get(x_39, 5);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_39);
x_54 = lean_ctor_get(x_12, 0);
lean_inc(x_54);
x_55 = l_Lean_FVarIdSet_insert(x_53, x_54);
x_56 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_48);
lean_ctor_set(x_56, 2, x_50);
lean_ctor_set(x_56, 3, x_51);
lean_ctor_set(x_56, 4, x_52);
lean_ctor_set(x_56, 5, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*6, x_49);
x_57 = lean_st_ref_set(x_4, x_56, x_40);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec_ref(x_57);
lean_inc(x_6);
x_22 = x_4;
x_23 = x_6;
x_24 = x_58;
goto block_36;
}
}
block_36:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_12, 2);
lean_inc_ref(x_25);
x_26 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(x_25, x_22, x_24);
lean_dec_ref(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(x_12, x_27, x_23, x_28);
lean_dec(x_23);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
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
uint8_t x_59; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_59 = !lean_is_exclusive(x_17);
if (x_59 == 0)
{
return x_17;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_17, 0);
x_61 = lean_ctor_get(x_17, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_17);
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
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_63 = !lean_is_exclusive(x_14);
if (x_63 == 0)
{
return x_14;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_14, 0);
x_65 = lean_ctor_get(x_14, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_14);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
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
lean_inc_ref(x_7);
lean_inc(x_2);
x_56 = l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec_ref(x_56);
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
lean_inc_ref(x_7);
x_64 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_60, x_63, x_4, x_7, x_8, x_58);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec_ref(x_64);
lean_inc(x_8);
lean_inc_ref(x_7);
x_67 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda(x_65, x_4, x_5, x_6, x_7, x_8, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec_ref(x_67);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_20 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__0(x_18, x_19, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
x_23 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_10, x_12, x_13, x_14, x_15, x_16, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_26 = l_Lean_Compiler_LCNF_ToLCNF_toCode(x_24, x_12, x_13, x_14, x_15, x_16, x_25);
lean_dec(x_12);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
lean_inc(x_27);
x_29 = l_Lean_Compiler_LCNF_Code_inferType(x_27, x_13, x_14, x_15, x_16, x_28);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
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
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
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
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
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
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_1, x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_9, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec_ref(x_5);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_box(1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__10;
x_15 = lean_st_mk_ref(x_14, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_18);
lean_dec(x_10);
x_19 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__11;
x_20 = 0;
x_21 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12;
x_22 = lean_box(0);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_12);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set(x_24, 5, x_13);
lean_ctor_set(x_24, 6, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*7, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*7 + 1, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*7 + 2, x_20);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_16);
x_25 = lean_infer_type(x_1, x_24, x_16, x_6, x_7, x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_st_ref_get(x_16, x_27);
lean_dec(x_16);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_apply_7(x_2, x_26, x_3, x_4, x_5, x_6, x_7, x_29);
return x_30;
}
else
{
lean_dec(x_16);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec_ref(x_25);
x_33 = lean_apply_7(x_2, x_31, x_3, x_4, x_5, x_6, x_7, x_32);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
return x_25;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_25);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__0___boxed), 7, 0);
lean_inc_ref(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__1), 8, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_10, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__0___boxed), 7, 0);
lean_inc_ref(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__1), 8, 2);
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
x_11 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22;
x_12 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_12);
x_13 = lean_mk_array(x_12, x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_12, x_14);
lean_dec(x_12);
lean_inc_ref(x_1);
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
lean_dec_ref(x_28);
x_30 = l_Lean_mkAppN(x_26, x_29);
lean_dec_ref(x_29);
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
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22;
x_10 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_10);
x_11 = lean_mk_array(x_10, x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_10, x_12);
lean_dec(x_10);
lean_inc_ref(x_1);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_11, x_13);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10;
x_28 = l_Lean_Expr_isAppOf(x_1, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11;
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
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22;
x_10 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_10);
x_11 = lean_mk_array(x_10, x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_10, x_12);
lean_dec(x_10);
lean_inc_ref(x_1);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_11, x_13);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6;
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
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22;
x_11 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_11);
x_12 = lean_mk_array(x_11, x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_11, x_13);
lean_dec(x_11);
lean_inc_ref(x_2);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_12, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___boxed), 8, 2);
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
x_3 = lean_unsigned_to_nat(591u);
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
x_3 = lean_unsigned_to_nat(595u);
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
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_1, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_unsigned_to_nat(5u);
x_20 = lean_array_get(x_2, x_3, x_19);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
x_21 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_20, x_10, x_11, x_12, x_13, x_14, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_32; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_32 = l_Lean_Expr_getAppFn(x_4);
if (lean_obj_tag(x_32) == 4)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_33);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
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
x_49 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15;
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_50 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_48, x_49, x_10, x_11, x_12, x_13, x_14, x_23);
if (lean_obj_tag(x_50) == 0)
{
switch (lean_obj_tag(x_17)) {
case 0:
{
uint8_t x_51; 
lean_free_object(x_33);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
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
lean_dec_ref(x_50);
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
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_61 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_33, x_49, x_10, x_11, x_12, x_13, x_14, x_56);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_62, x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_63);
return x_64;
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
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
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_69 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_33, x_49, x_10, x_11, x_12, x_13, x_14, x_56);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_70, x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_71);
return x_72;
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
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
lean_dec_ref(x_17);
lean_dec(x_9);
x_73 = lean_ctor_get(x_50, 1);
lean_inc(x_73);
lean_dec_ref(x_50);
x_74 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__4;
x_75 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8(x_74, x_10, x_11, x_12, x_13, x_14, x_73);
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
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
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
x_89 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15;
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_90 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_88, x_89, x_10, x_11, x_12, x_13, x_14, x_23);
if (lean_obj_tag(x_90) == 0)
{
switch (lean_obj_tag(x_17)) {
case 0:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
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
lean_dec_ref(x_90);
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
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_102 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_101, x_89, x_10, x_11, x_12, x_13, x_14, x_95);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec_ref(x_102);
x_105 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_103, x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_104);
return x_105;
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_102;
}
}
default: 
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec_ref(x_17);
lean_dec(x_9);
x_106 = lean_ctor_get(x_90, 1);
lean_inc(x_106);
lean_dec_ref(x_90);
x_107 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__4;
x_108 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8(x_107, x_10, x_11, x_12, x_13, x_14, x_106);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
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
lean_dec_ref(x_36);
lean_dec_ref(x_33);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
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
x_125 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__15;
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_126 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_124, x_125, x_10, x_11, x_12, x_13, x_14, x_23);
if (lean_obj_tag(x_126) == 0)
{
switch (lean_obj_tag(x_17)) {
case 0:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_115);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
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
lean_dec_ref(x_126);
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
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_138 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_137, x_125, x_10, x_11, x_12, x_13, x_14, x_131);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec_ref(x_138);
x_141 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_139, x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_140);
return x_141;
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_138;
}
}
default: 
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_115);
lean_dec_ref(x_17);
lean_dec(x_9);
x_142 = lean_ctor_get(x_126, 1);
lean_inc(x_142);
lean_dec_ref(x_126);
x_143 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__4;
x_144 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8(x_143, x_10, x_11, x_12, x_13, x_14, x_142);
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
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
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
lean_dec_ref(x_113);
lean_dec_ref(x_33);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_32);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
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
x_30 = l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8(x_29, x_24, x_25, x_26, x_27, x_28, x_23);
return x_30;
}
}
else
{
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_21;
}
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
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
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22;
x_11 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_11);
x_12 = lean_mk_array(x_11, x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_11, x_13);
lean_dec(x_11);
lean_inc_ref(x_1);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_12, x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get(x_8, x_15, x_16);
x_18 = lean_array_get(x_8, x_15, x_13);
x_19 = lean_unsigned_to_nat(3u);
x_20 = lean_array_get(x_8, x_15, x_19);
lean_inc_ref(x_1);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__2___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0_spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5_spec__5___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5_spec__5(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__5(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
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
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0___boxed(lean_object** _args) {
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
x_19 = lean_unbox(x_3);
x_20 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__0(x_1, x_2, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0___boxed(lean_object** _args) {
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
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_2);
x_19 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__0(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_toCode(x_9, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_2);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_object* initialize_Lean_Compiler_NeverExtractAttr(uint8_t builtin, lean_object*);
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
res = initialize_Lean_Compiler_NeverExtractAttr(builtin, lean_io_mk_world());
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
l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__0 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__0();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__0);
l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__1 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__1();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__1);
l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__2 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__2();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__2);
l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__3 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__3();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__3);
l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__4 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__4();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__4);
l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__5 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__5();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__5);
l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__6 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__6();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__6);
l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__7 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__7();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__9___redArg___closed__7);
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
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__17 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__17);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__18 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__18);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__19 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__19();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__19);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__20 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__20();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__20);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__21 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__21();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__21);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__22 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__22();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__22);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__23 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__23();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__23);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__24 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__24();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__24);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__25 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__25();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__25);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__26 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__26();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__26);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__27 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__27();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__27);
l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__28 = _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__28();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__28);
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
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__12);
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
l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__1);
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
l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___closed__0();
l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__0___redArg___closed__2);
l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__0 = _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__0();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__0);
l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__1 = _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__1();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__1);
l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__2 = _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__2();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__2);
l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__3 = _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__3();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__3);
l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__4 = _init_l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__4();
lean_mark_persistent(l_panic___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__8___closed__4);
l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__0 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__0();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__0);
l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__1);
l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__2);
l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__3);
l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__4);
l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__5);
l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__9___redArg___closed__6);
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
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___closed__0 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___closed__0();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___closed__0);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__2 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__2);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__4 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__4();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__4);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__5 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__5();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0_spec__0_spec__0___closed__5);
l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__0);
l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__1);
l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__2 = _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__2);
l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__3 = _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__3();
lean_mark_persistent(l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstInfo___at___Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__0_spec__0_spec__0___redArg___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__0 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__0);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___closed__1);
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
