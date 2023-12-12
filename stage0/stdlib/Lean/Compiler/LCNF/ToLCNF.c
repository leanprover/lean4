// Lean compiler output
// Module: Lean.Compiler.LCNF.ToLCNF
// Imports: Init Lean.ProjFns Lean.Compiler.BorrowedAnnotation Lean.Compiler.LCNF.Types Lean.Compiler.LCNF.Bind Lean.Compiler.LCNF.InferType Lean.Compiler.LCNF.Util
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
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__1;
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__3;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_litToValue(lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__3;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__7;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_LCNF_ToLCNF_applyToAny___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__13;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_builtinRuntimeTypes;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__2;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2;
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__2___boxed(lean_object*, lean_object*);
uint8_t l_List_elem___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7;
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___closed__1;
static lean_object* l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__1;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Compiler_LCNF_ToLCNF_bindCases___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__15;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqLocalInstance___boxed(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__4(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__21;
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__14;
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3;
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__7(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_cache___default;
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2;
lean_object* l_Lean_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22;
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__4;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__3;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MapDeclarationExtension_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11;
extern lean_object* l_Lean_Expr_instBEqExpr;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__4;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__4;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__3(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_isLCProof(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_projectionFnInfoExt;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__4;
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__2(lean_object*, lean_object*);
lean_object* l_instHashableArray___rarg___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__4(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_toAny___default;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_litToValue___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_appendTrees___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getCtorArity_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1;
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__8;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__2;
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default;
lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_joinTypes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t l_Lean_Compiler_LCNF_isPredicateType(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__20;
lean_object* l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__12;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__3(lean_object*, lean_object*);
uint8_t lean_is_marked_borrowed(lean_object*);
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__18;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__5;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9;
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__1;
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
extern lean_object* l_Lean_Expr_instHashableExpr;
lean_object* l_Lean_Meta_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__3;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__1(lean_object*, lean_object*, uint8_t);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___boxed(lean_object*);
lean_object* l_Lean_instHashableLocalInstance___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__3;
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isConstructorApp_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__1;
lean_object* l_Lean_Meta_whnf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__17;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__4;
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedArg;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4;
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__4___boxed(lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default___spec__1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_CasesInfo_numAlts(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__10;
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6;
uint8_t l_Lean_BinderInfo_isImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mod(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
size_t lean_hashmap_mk_idx(lean_object*, uint64_t);
extern lean_object* l_Lean_instInhabitedProjectionFunctionInfo;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3;
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_toCtorIfLit(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__19;
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__16;
lean_object* l_Lean_Compiler_LCNF_getCasesInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__4;
lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_Cache_new(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__6;
lean_object* l_Lean_Compiler_LCNF_mkParam(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__2(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(uint8_t, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__5;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__5;
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_letFunAnnotation_x3f(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_RBNode_isBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__5;
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__3;
static size_t l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__5;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1;
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__3;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_LCNF_ToLCNF_applyToAny___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default;
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__2;
extern lean_object* l_Lean_noConfusionExt;
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Param_toExpr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__16;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_seq___default;
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10;
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Compiler_LCNF_ToLCNF_bindCases___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__4;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__1(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_cache___default___closed__1;
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Array_instBEqArray___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__2;
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_Cache_store(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__11;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__14;
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__8(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lcProof", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_isLCProof(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__2;
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
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__1;
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_3 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__2;
x_4 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__3;
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = l_Lean_Compiler_LCNF_findFunDecl_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Compiler_LCNF_findLetValue_x3f(x_1, x_2, x_3, x_4, x_5, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
if (lean_obj_tag(x_18) == 4)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_10, 1);
x_21 = lean_ctor_get(x_10, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_array_get_size(x_23);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_22);
x_27 = lean_box(0);
lean_ctor_set(x_10, 0, x_27);
return x_10;
}
else
{
lean_free_object(x_10);
x_1 = x_22;
x_6 = x_20;
goto _start;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_ctor_get(x_18, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_dec(x_18);
x_32 = lean_array_get_size(x_31);
lean_dec(x_31);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_eq(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_30);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
else
{
x_1 = x_30;
x_6 = x_29;
goto _start;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_18);
x_38 = !lean_is_exclusive(x_10);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_10, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_10, 0, x_40);
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 1);
lean_inc(x_41);
lean_dec(x_10);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_7);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_7, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_8);
if (x_46 == 0)
{
return x_7;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_8, 0);
lean_inc(x_47);
lean_dec(x_8);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_7, 0, x_48);
return x_7;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_7, 1);
lean_inc(x_49);
lean_dec(x_7);
x_50 = lean_ctor_get(x_8, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_51 = x_8;
} else {
 lean_dec_ref(x_8);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
}
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
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__3(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = l_Lean_Name_quickCmp(x_1, x_6);
switch (x_9) {
case 0:
{
uint8_t x_10; 
x_10 = l_Lean_RBNode_isBlack___rarg(x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_RBNode_del___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__3(x_1, x_5);
x_12 = 0;
lean_ctor_set(x_2, 0, x_11);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_2);
x_13 = l_Lean_RBNode_del___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__3(x_1, x_5);
x_14 = l_Lean_RBNode_balLeft___rarg(x_13, x_6, x_7, x_8);
return x_14;
}
}
case 1:
{
lean_object* x_15; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
x_15 = l_Lean_RBNode_appendTrees___rarg(x_5, x_8);
return x_15;
}
default: 
{
uint8_t x_16; 
x_16 = l_Lean_RBNode_isBlack___rarg(x_8);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_RBNode_del___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__3(x_1, x_8);
x_18 = 0;
lean_ctor_set(x_2, 3, x_17);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_18);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_2);
x_19 = l_Lean_RBNode_del___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__3(x_1, x_8);
x_20 = l_Lean_RBNode_balRight___rarg(x_5, x_6, x_7, x_19);
return x_20;
}
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_25 = l_Lean_Name_quickCmp(x_1, x_22);
switch (x_25) {
case 0:
{
uint8_t x_26; 
x_26 = l_Lean_RBNode_isBlack___rarg(x_21);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = l_Lean_RBNode_del___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__3(x_1, x_21);
x_28 = 0;
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_23);
lean_ctor_set(x_29, 3, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_RBNode_del___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__3(x_1, x_21);
x_31 = l_Lean_RBNode_balLeft___rarg(x_30, x_22, x_23, x_24);
return x_31;
}
}
case 1:
{
lean_object* x_32; 
lean_dec(x_23);
lean_dec(x_22);
x_32 = l_Lean_RBNode_appendTrees___rarg(x_21, x_24);
return x_32;
}
default: 
{
uint8_t x_33; 
x_33 = l_Lean_RBNode_isBlack___rarg(x_24);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = l_Lean_RBNode_del___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__3(x_1, x_24);
x_35 = 0;
x_36 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_RBNode_del___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__3(x_1, x_24);
x_38 = l_Lean_RBNode_balRight___rarg(x_21, x_22, x_23, x_37);
return x_38;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_del___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__3(x_1, x_2);
x_4 = l_Lean_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_array_uget(x_13, x_3);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_14, 2);
lean_inc(x_19);
x_20 = 1;
lean_inc(x_18);
x_21 = l_Lean_Compiler_LCNF_replaceExprFVars(x_19, x_18, x_20, x_6, x_7, x_8, x_9, x_10);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 0;
x_25 = l_Lean_Compiler_LCNF_mkAuxParam(x_22, x_24, x_6, x_7, x_8, x_9, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_26);
x_28 = lean_array_push(x_17, x_26);
x_29 = lean_ctor_get(x_14, 0);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
lean_inc(x_30);
x_31 = l_Lean_Expr_fvar___override(x_30);
x_32 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_18, x_29, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_34 = lean_array_push(x_15, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = 1;
x_38 = lean_usize_add(x_3, x_37);
x_3 = x_38;
x_4 = x_36;
x_10 = x_27;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_uget(x_4, x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_4, x_3, x_14);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
x_19 = lean_ctor_get(x_13, 2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_19, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set(x_13, 2, x_21);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_15, x_3, x_13);
x_3 = x_24;
x_4 = x_25;
x_10 = x_22;
goto _start;
}
else
{
uint8_t x_27; 
lean_free_object(x_13);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
x_33 = lean_ctor_get(x_13, 2);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_34 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_33, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_32);
lean_ctor_set(x_37, 2, x_35);
x_38 = 1;
x_39 = lean_usize_add(x_3, x_38);
x_40 = lean_array_uset(x_15, x_3, x_37);
x_3 = x_39;
x_4 = x_40;
x_10 = x_36;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_42 = lean_ctor_get(x_34, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_44 = x_34;
} else {
 lean_dec_ref(x_34);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_13);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_13, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_48 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_47, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_ctor_set(x_13, 0, x_49);
x_51 = 1;
x_52 = lean_usize_add(x_3, x_51);
x_53 = lean_array_uset(x_15, x_3, x_13);
x_3 = x_52;
x_4 = x_53;
x_10 = x_50;
goto _start;
}
else
{
uint8_t x_55; 
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_48);
if (x_55 == 0)
{
return x_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_48);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_13, 0);
lean_inc(x_59);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_60 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_59, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_61);
x_64 = 1;
x_65 = lean_usize_add(x_3, x_64);
x_66 = lean_array_uset(x_15, x_3, x_63);
x_3 = x_65;
x_4 = x_66;
x_10 = x_62;
goto _start;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_68 = lean_ctor_get(x_60, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_60, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_70 = x_60;
} else {
 lean_dec_ref(x_60);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
}
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__3;
x_3 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__4;
x_4 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__5;
x_5 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_2);
lean_ctor_set(x_5, 7, x_3);
lean_ctor_set(x_5, 8, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_4, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_16);
x_18 = lean_ctor_get(x_5, 2);
x_19 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__6;
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
lean_inc(x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_25);
x_27 = lean_ctor_get(x_5, 2);
x_28 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__6;
lean_inc(x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
x_30 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_1);
lean_inc(x_8);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_5);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_5, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__1(x_16, x_18);
lean_dec(x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_free_object(x_14);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_take(x_5, x_17);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_RBNode_erase___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__2(x_18, x_23);
lean_dec(x_18);
x_26 = lean_st_ref_set(x_5, x_25, x_24);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_12);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_12);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_3);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
x_37 = lean_ctor_get(x_3, 0);
lean_inc(x_37);
x_38 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__1(x_35, x_37);
lean_dec(x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_37);
lean_dec(x_5);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_12);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_st_ref_take(x_5, x_36);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_RBNode_erase___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__2(x_37, x_43);
lean_dec(x_37);
x_46 = lean_st_ref_set(x_5, x_45, x_44);
lean_dec(x_5);
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
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_12);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_3);
lean_ctor_set(x_50, 1, x_49);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_5);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_Compiler_LCNF_mkCasesResultType(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_1);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_3);
lean_ctor_set(x_18, 3, x_1);
x_19 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_alt", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_x", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_jp", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("`Code.bind` failed, empty `cases` found", 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
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
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 5)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_name_eq(x_14, x_13);
lean_dec(x_13);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_2);
x_16 = lean_box(0);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_11, x_16, x_3, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_11, 3);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 4)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_22 = l_Lean_Compiler_LCNF_getBinderName(x_20, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Name_getPrefix(x_23);
lean_dec(x_23);
x_26 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2;
x_27 = lean_name_eq(x_25, x_26);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_free_object(x_18);
lean_dec(x_21);
lean_dec(x_20);
lean_free_object(x_2);
x_28 = lean_box(0);
x_29 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_11, x_28, x_3, x_4, x_5, x_6, x_7, x_24);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_inc(x_20);
x_30 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(x_20, x_4, x_5, x_6, x_7, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_18);
lean_dec(x_21);
lean_dec(x_20);
lean_free_object(x_2);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_11, x_33, x_3, x_4, x_5, x_6, x_7, x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_9);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
x_37 = l_Lean_Compiler_LCNF_eraseLetDecl(x_11, x_4, x_5, x_6, x_7, x_35);
lean_dec(x_11);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_st_ref_get(x_3, x_38);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__1(x_41, x_20);
lean_dec(x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; lean_object* x_55; size_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_free_object(x_39);
x_44 = lean_unsigned_to_nat(8u);
x_45 = l_Lean_mkHashMapImp___rarg(x_44);
x_46 = lean_ctor_get(x_36, 2);
lean_inc(x_46);
lean_dec(x_36);
x_47 = lean_array_get_size(x_21);
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_Array_toSubarray___rarg(x_46, x_48, x_47);
x_50 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_ctor_get(x_49, 2);
lean_inc(x_53);
x_54 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
x_56 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_57 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__5(x_49, x_54, x_56, x_52, x_3, x_4, x_5, x_6, x_7, x_42);
lean_dec(x_49);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
lean_dec(x_59);
lean_inc(x_20);
lean_ctor_set(x_18, 1, x_61);
x_63 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_64 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_18, x_63, x_4, x_5, x_6, x_7, x_60);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
lean_dec(x_1);
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5;
x_71 = lean_array_push(x_70, x_69);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 1, x_71);
lean_ctor_set(x_2, 0, x_67);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_65);
lean_ctor_set(x_72, 1, x_2);
x_73 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7;
x_74 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_62, x_72, x_73, x_4, x_5, x_6, x_7, x_66);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_st_ref_take(x_3, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_75);
x_80 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_78, x_20, x_75);
x_81 = lean_st_ref_set(x_3, x_80, x_79);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
x_84 = lean_ctor_get(x_75, 0);
lean_inc(x_84);
lean_dec(x_75);
x_85 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_21);
lean_ctor_set(x_81, 0, x_85);
return x_81;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_dec(x_81);
x_87 = lean_ctor_get(x_75, 0);
lean_inc(x_87);
lean_dec(x_75);
x_88 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_21);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_90 = !lean_is_exclusive(x_74);
if (x_90 == 0)
{
return x_74;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_74, 0);
x_92 = lean_ctor_get(x_74, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_74);
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
lean_dec(x_62);
lean_dec(x_21);
lean_dec(x_20);
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_64);
if (x_94 == 0)
{
return x_64;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_64, 0);
x_96 = lean_ctor_get(x_64, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_64);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_36);
lean_free_object(x_18);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_98 = lean_ctor_get(x_43, 0);
lean_inc(x_98);
lean_dec(x_43);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec(x_98);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 1, x_21);
lean_ctor_set(x_2, 0, x_99);
lean_ctor_set(x_39, 0, x_2);
return x_39;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_39, 0);
x_101 = lean_ctor_get(x_39, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_39);
x_102 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__1(x_100, x_20);
lean_dec(x_100);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; size_t x_113; lean_object* x_114; size_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_103 = lean_unsigned_to_nat(8u);
x_104 = l_Lean_mkHashMapImp___rarg(x_103);
x_105 = lean_ctor_get(x_36, 2);
lean_inc(x_105);
lean_dec(x_36);
x_106 = lean_array_get_size(x_21);
x_107 = lean_unsigned_to_nat(0u);
x_108 = l_Array_toSubarray___rarg(x_105, x_107, x_106);
x_109 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_104);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_ctor_get(x_108, 2);
lean_inc(x_112);
x_113 = lean_usize_of_nat(x_112);
lean_dec(x_112);
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
x_115 = lean_usize_of_nat(x_114);
lean_dec(x_114);
x_116 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__5(x_108, x_113, x_115, x_111, x_3, x_4, x_5, x_6, x_7, x_101);
lean_dec(x_108);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_dec(x_116);
x_120 = lean_ctor_get(x_117, 0);
lean_inc(x_120);
lean_dec(x_117);
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
lean_dec(x_118);
lean_inc(x_20);
lean_ctor_set(x_18, 1, x_120);
x_122 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_123 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_18, x_122, x_4, x_5, x_6, x_7, x_119);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_ctor_get(x_1, 0);
lean_inc(x_126);
lean_dec(x_1);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5;
x_130 = lean_array_push(x_129, x_128);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 1, x_130);
lean_ctor_set(x_2, 0, x_126);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_124);
lean_ctor_set(x_131, 1, x_2);
x_132 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7;
x_133 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_121, x_131, x_132, x_4, x_5, x_6, x_7, x_125);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_st_ref_take(x_3, x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
lean_inc(x_134);
x_139 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_137, x_20, x_134);
x_140 = lean_st_ref_set(x_3, x_139, x_138);
lean_dec(x_3);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_142 = x_140;
} else {
 lean_dec_ref(x_140);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_134, 0);
lean_inc(x_143);
lean_dec(x_134);
x_144 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_21);
if (lean_is_scalar(x_142)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_142;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_141);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_146 = lean_ctor_get(x_133, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_133, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_148 = x_133;
} else {
 lean_dec_ref(x_133);
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
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_121);
lean_dec(x_21);
lean_dec(x_20);
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_150 = lean_ctor_get(x_123, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_123, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_152 = x_123;
} else {
 lean_dec_ref(x_123);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_36);
lean_free_object(x_18);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_154 = lean_ctor_get(x_102, 0);
lean_inc(x_154);
lean_dec(x_102);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec(x_154);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 1, x_21);
lean_ctor_set(x_2, 0, x_155);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_2);
lean_ctor_set(x_156, 1, x_101);
return x_156;
}
}
}
}
}
else
{
uint8_t x_157; 
lean_free_object(x_18);
lean_dec(x_21);
lean_dec(x_20);
lean_free_object(x_2);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_22);
if (x_157 == 0)
{
return x_22;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_22, 0);
x_159 = lean_ctor_get(x_22, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_22);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_18, 0);
x_162 = lean_ctor_get(x_18, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_18);
lean_inc(x_161);
x_163 = l_Lean_Compiler_LCNF_getBinderName(x_161, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = l_Lean_Name_getPrefix(x_164);
lean_dec(x_164);
x_167 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2;
x_168 = lean_name_eq(x_166, x_167);
lean_dec(x_166);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_162);
lean_dec(x_161);
lean_free_object(x_2);
x_169 = lean_box(0);
x_170 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_11, x_169, x_3, x_4, x_5, x_6, x_7, x_165);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_inc(x_161);
x_171 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(x_161, x_4, x_5, x_6, x_7, x_165);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_162);
lean_dec(x_161);
lean_free_object(x_2);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_box(0);
x_175 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_11, x_174, x_3, x_4, x_5, x_6, x_7, x_173);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_9);
x_176 = lean_ctor_get(x_171, 1);
lean_inc(x_176);
lean_dec(x_171);
x_177 = lean_ctor_get(x_172, 0);
lean_inc(x_177);
lean_dec(x_172);
x_178 = l_Lean_Compiler_LCNF_eraseLetDecl(x_11, x_4, x_5, x_6, x_7, x_176);
lean_dec(x_11);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_180 = lean_st_ref_get(x_3, x_179);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_183 = x_180;
} else {
 lean_dec_ref(x_180);
 x_183 = lean_box(0);
}
x_184 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__1(x_181, x_161);
lean_dec(x_181);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; size_t x_195; lean_object* x_196; size_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_183);
x_185 = lean_unsigned_to_nat(8u);
x_186 = l_Lean_mkHashMapImp___rarg(x_185);
x_187 = lean_ctor_get(x_177, 2);
lean_inc(x_187);
lean_dec(x_177);
x_188 = lean_array_get_size(x_162);
x_189 = lean_unsigned_to_nat(0u);
x_190 = l_Array_toSubarray___rarg(x_187, x_189, x_188);
x_191 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_186);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_ctor_get(x_190, 2);
lean_inc(x_194);
x_195 = lean_usize_of_nat(x_194);
lean_dec(x_194);
x_196 = lean_ctor_get(x_190, 1);
lean_inc(x_196);
x_197 = lean_usize_of_nat(x_196);
lean_dec(x_196);
x_198 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__5(x_190, x_195, x_197, x_193, x_3, x_4, x_5, x_6, x_7, x_182);
lean_dec(x_190);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_dec(x_198);
x_202 = lean_ctor_get(x_199, 0);
lean_inc(x_202);
lean_dec(x_199);
x_203 = lean_ctor_get(x_200, 0);
lean_inc(x_203);
lean_dec(x_200);
lean_inc(x_161);
x_204 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_204, 0, x_161);
lean_ctor_set(x_204, 1, x_202);
x_205 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_206 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_204, x_205, x_4, x_5, x_6, x_7, x_201);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_ctor_get(x_1, 0);
lean_inc(x_209);
lean_dec(x_1);
x_210 = lean_ctor_get(x_207, 0);
lean_inc(x_210);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_210);
x_212 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5;
x_213 = lean_array_push(x_212, x_211);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 1, x_213);
lean_ctor_set(x_2, 0, x_209);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_207);
lean_ctor_set(x_214, 1, x_2);
x_215 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7;
x_216 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_203, x_214, x_215, x_4, x_5, x_6, x_7, x_208);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_st_ref_take(x_3, x_218);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
lean_inc(x_217);
x_222 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_220, x_161, x_217);
x_223 = lean_st_ref_set(x_3, x_222, x_221);
lean_dec(x_3);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_225 = x_223;
} else {
 lean_dec_ref(x_223);
 x_225 = lean_box(0);
}
x_226 = lean_ctor_get(x_217, 0);
lean_inc(x_226);
lean_dec(x_217);
x_227 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_162);
if (lean_is_scalar(x_225)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_225;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_224);
return x_228;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_3);
x_229 = lean_ctor_get(x_216, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_216, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_231 = x_216;
} else {
 lean_dec_ref(x_216);
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
lean_dec(x_203);
lean_dec(x_162);
lean_dec(x_161);
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_233 = lean_ctor_get(x_206, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_206, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_235 = x_206;
} else {
 lean_dec_ref(x_206);
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
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_177);
lean_dec(x_161);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_237 = lean_ctor_get(x_184, 0);
lean_inc(x_237);
lean_dec(x_184);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
lean_dec(x_237);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 1, x_162);
lean_ctor_set(x_2, 0, x_238);
if (lean_is_scalar(x_183)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_183;
}
lean_ctor_set(x_239, 0, x_2);
lean_ctor_set(x_239, 1, x_182);
return x_239;
}
}
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_162);
lean_dec(x_161);
lean_free_object(x_2);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_240 = lean_ctor_get(x_163, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_163, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_242 = x_163;
} else {
 lean_dec_ref(x_163);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
return x_243;
}
}
}
else
{
lean_object* x_244; lean_object* x_245; 
lean_dec(x_18);
lean_free_object(x_2);
x_244 = lean_box(0);
x_245 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_11, x_244, x_3, x_4, x_5, x_6, x_7, x_8);
return x_245;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_246 = lean_ctor_get(x_2, 0);
lean_inc(x_246);
lean_dec(x_2);
x_247 = lean_ctor_get(x_9, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 0);
lean_inc(x_248);
x_249 = lean_name_eq(x_248, x_247);
lean_dec(x_247);
lean_dec(x_248);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_box(0);
x_251 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_246, x_250, x_3, x_4, x_5, x_6, x_7, x_8);
return x_251;
}
else
{
lean_object* x_252; 
x_252 = lean_ctor_get(x_246, 3);
lean_inc(x_252);
if (lean_obj_tag(x_252) == 4)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_255 = x_252;
} else {
 lean_dec_ref(x_252);
 x_255 = lean_box(0);
}
lean_inc(x_253);
x_256 = l_Lean_Compiler_LCNF_getBinderName(x_253, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = l_Lean_Name_getPrefix(x_257);
lean_dec(x_257);
x_260 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2;
x_261 = lean_name_eq(x_259, x_260);
lean_dec(x_259);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
x_262 = lean_box(0);
x_263 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_246, x_262, x_3, x_4, x_5, x_6, x_7, x_258);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; 
lean_inc(x_253);
x_264 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(x_253, x_4, x_5, x_6, x_7, x_258);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = lean_box(0);
x_268 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_246, x_267, x_3, x_4, x_5, x_6, x_7, x_266);
return x_268;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_9);
x_269 = lean_ctor_get(x_264, 1);
lean_inc(x_269);
lean_dec(x_264);
x_270 = lean_ctor_get(x_265, 0);
lean_inc(x_270);
lean_dec(x_265);
x_271 = l_Lean_Compiler_LCNF_eraseLetDecl(x_246, x_4, x_5, x_6, x_7, x_269);
lean_dec(x_246);
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
lean_dec(x_271);
x_273 = lean_st_ref_get(x_3, x_272);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_276 = x_273;
} else {
 lean_dec_ref(x_273);
 x_276 = lean_box(0);
}
x_277 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__1(x_274, x_253);
lean_dec(x_274);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; size_t x_288; lean_object* x_289; size_t x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_276);
x_278 = lean_unsigned_to_nat(8u);
x_279 = l_Lean_mkHashMapImp___rarg(x_278);
x_280 = lean_ctor_get(x_270, 2);
lean_inc(x_280);
lean_dec(x_270);
x_281 = lean_array_get_size(x_254);
x_282 = lean_unsigned_to_nat(0u);
x_283 = l_Array_toSubarray___rarg(x_280, x_282, x_281);
x_284 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_279);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_ctor_get(x_283, 2);
lean_inc(x_287);
x_288 = lean_usize_of_nat(x_287);
lean_dec(x_287);
x_289 = lean_ctor_get(x_283, 1);
lean_inc(x_289);
x_290 = lean_usize_of_nat(x_289);
lean_dec(x_289);
x_291 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__5(x_283, x_288, x_290, x_286, x_3, x_4, x_5, x_6, x_7, x_275);
lean_dec(x_283);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
x_294 = lean_ctor_get(x_291, 1);
lean_inc(x_294);
lean_dec(x_291);
x_295 = lean_ctor_get(x_292, 0);
lean_inc(x_295);
lean_dec(x_292);
x_296 = lean_ctor_get(x_293, 0);
lean_inc(x_296);
lean_dec(x_293);
lean_inc(x_253);
if (lean_is_scalar(x_255)) {
 x_297 = lean_alloc_ctor(4, 2, 0);
} else {
 x_297 = x_255;
}
lean_ctor_set(x_297, 0, x_253);
lean_ctor_set(x_297, 1, x_295);
x_298 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_299 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_297, x_298, x_4, x_5, x_6, x_7, x_294);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_ctor_get(x_1, 0);
lean_inc(x_302);
lean_dec(x_1);
x_303 = lean_ctor_get(x_300, 0);
lean_inc(x_303);
x_304 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_304, 0, x_303);
x_305 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5;
x_306 = lean_array_push(x_305, x_304);
x_307 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_307, 0, x_302);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_300);
lean_ctor_set(x_308, 1, x_307);
x_309 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7;
x_310 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_296, x_308, x_309, x_4, x_5, x_6, x_7, x_301);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
x_313 = lean_st_ref_take(x_3, x_312);
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
lean_inc(x_311);
x_316 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_314, x_253, x_311);
x_317 = lean_st_ref_set(x_3, x_316, x_315);
lean_dec(x_3);
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_319 = x_317;
} else {
 lean_dec_ref(x_317);
 x_319 = lean_box(0);
}
x_320 = lean_ctor_get(x_311, 0);
lean_inc(x_320);
lean_dec(x_311);
x_321 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_254);
if (lean_is_scalar(x_319)) {
 x_322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_322 = x_319;
}
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_318);
return x_322;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_3);
x_323 = lean_ctor_get(x_310, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_310, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_325 = x_310;
} else {
 lean_dec_ref(x_310);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 2, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_323);
lean_ctor_set(x_326, 1, x_324);
return x_326;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_296);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_327 = lean_ctor_get(x_299, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_299, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_329 = x_299;
} else {
 lean_dec_ref(x_299);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 2, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_327);
lean_ctor_set(x_330, 1, x_328);
return x_330;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_270);
lean_dec(x_255);
lean_dec(x_253);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_331 = lean_ctor_get(x_277, 0);
lean_inc(x_331);
lean_dec(x_277);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
lean_dec(x_331);
x_333 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_254);
if (lean_is_scalar(x_276)) {
 x_334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_334 = x_276;
}
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_275);
return x_334;
}
}
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_246);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_335 = lean_ctor_get(x_256, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_256, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_337 = x_256;
} else {
 lean_dec_ref(x_256);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_336);
return x_338;
}
}
else
{
lean_object* x_339; lean_object* x_340; 
lean_dec(x_252);
x_339 = lean_box(0);
x_340 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_246, x_339, x_3, x_4, x_5, x_6, x_7, x_8);
return x_340;
}
}
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_2, 0);
lean_inc(x_341);
lean_dec(x_2);
x_342 = lean_box(0);
x_343 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_341, x_342, x_3, x_4, x_5, x_6, x_7, x_8);
return x_343;
}
}
case 1:
{
uint8_t x_344; 
x_344 = !lean_is_exclusive(x_2);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_2, 0);
x_346 = lean_ctor_get(x_2, 1);
x_347 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_346, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_347) == 0)
{
uint8_t x_348; 
x_348 = !lean_is_exclusive(x_347);
if (x_348 == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_347, 0);
lean_ctor_set(x_2, 1, x_349);
lean_ctor_set(x_347, 0, x_2);
return x_347;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_347, 0);
x_351 = lean_ctor_get(x_347, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_347);
lean_ctor_set(x_2, 1, x_350);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_2);
lean_ctor_set(x_352, 1, x_351);
return x_352;
}
}
else
{
uint8_t x_353; 
lean_free_object(x_2);
lean_dec(x_345);
x_353 = !lean_is_exclusive(x_347);
if (x_353 == 0)
{
return x_347;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_ctor_get(x_347, 0);
x_355 = lean_ctor_get(x_347, 1);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_347);
x_356 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_355);
return x_356;
}
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_357 = lean_ctor_get(x_2, 0);
x_358 = lean_ctor_get(x_2, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_2);
x_359 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_358, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_362 = x_359;
} else {
 lean_dec_ref(x_359);
 x_362 = lean_box(0);
}
x_363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_363, 0, x_357);
lean_ctor_set(x_363, 1, x_360);
if (lean_is_scalar(x_362)) {
 x_364 = lean_alloc_ctor(0, 2, 0);
} else {
 x_364 = x_362;
}
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_361);
return x_364;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_dec(x_357);
x_365 = lean_ctor_get(x_359, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_359, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_367 = x_359;
} else {
 lean_dec_ref(x_359);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(1, 2, 0);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_365);
lean_ctor_set(x_368, 1, x_366);
return x_368;
}
}
}
case 2:
{
uint8_t x_369; 
x_369 = !lean_is_exclusive(x_2);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_370 = lean_ctor_get(x_2, 0);
x_371 = lean_ctor_get(x_2, 1);
x_372 = lean_ctor_get(x_370, 4);
lean_inc(x_372);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_373 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_372, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
x_376 = lean_ctor_get(x_370, 2);
lean_inc(x_376);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_374);
lean_inc(x_376);
x_377 = l_Lean_Compiler_LCNF_Code_inferParamType(x_376, x_374, x_4, x_5, x_6, x_7, x_375);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
x_380 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_370, x_378, x_376, x_374, x_4, x_5, x_6, x_7, x_379);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
x_383 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_371, x_3, x_4, x_5, x_6, x_7, x_382);
if (lean_obj_tag(x_383) == 0)
{
uint8_t x_384; 
x_384 = !lean_is_exclusive(x_383);
if (x_384 == 0)
{
lean_object* x_385; 
x_385 = lean_ctor_get(x_383, 0);
lean_ctor_set(x_2, 1, x_385);
lean_ctor_set(x_2, 0, x_381);
lean_ctor_set(x_383, 0, x_2);
return x_383;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_383, 0);
x_387 = lean_ctor_get(x_383, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_383);
lean_ctor_set(x_2, 1, x_386);
lean_ctor_set(x_2, 0, x_381);
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_2);
lean_ctor_set(x_388, 1, x_387);
return x_388;
}
}
else
{
uint8_t x_389; 
lean_dec(x_381);
lean_free_object(x_2);
x_389 = !lean_is_exclusive(x_383);
if (x_389 == 0)
{
return x_383;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_383, 0);
x_391 = lean_ctor_get(x_383, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_383);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
return x_392;
}
}
}
else
{
uint8_t x_393; 
lean_dec(x_376);
lean_dec(x_374);
lean_free_object(x_2);
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_393 = !lean_is_exclusive(x_377);
if (x_393 == 0)
{
return x_377;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_377, 0);
x_395 = lean_ctor_get(x_377, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_377);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
}
else
{
uint8_t x_397; 
lean_free_object(x_2);
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_397 = !lean_is_exclusive(x_373);
if (x_397 == 0)
{
return x_373;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_373, 0);
x_399 = lean_ctor_get(x_373, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_373);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_401 = lean_ctor_get(x_2, 0);
x_402 = lean_ctor_get(x_2, 1);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_2);
x_403 = lean_ctor_get(x_401, 4);
lean_inc(x_403);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_404 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_403, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
lean_dec(x_404);
x_407 = lean_ctor_get(x_401, 2);
lean_inc(x_407);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_405);
lean_inc(x_407);
x_408 = l_Lean_Compiler_LCNF_Code_inferParamType(x_407, x_405, x_4, x_5, x_6, x_7, x_406);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
x_411 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_401, x_409, x_407, x_405, x_4, x_5, x_6, x_7, x_410);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_402, x_3, x_4, x_5, x_6, x_7, x_413);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_417 = x_414;
} else {
 lean_dec_ref(x_414);
 x_417 = lean_box(0);
}
x_418 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_418, 0, x_412);
lean_ctor_set(x_418, 1, x_415);
if (lean_is_scalar(x_417)) {
 x_419 = lean_alloc_ctor(0, 2, 0);
} else {
 x_419 = x_417;
}
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_416);
return x_419;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_412);
x_420 = lean_ctor_get(x_414, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_414, 1);
lean_inc(x_421);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_422 = x_414;
} else {
 lean_dec_ref(x_414);
 x_422 = lean_box(0);
}
if (lean_is_scalar(x_422)) {
 x_423 = lean_alloc_ctor(1, 2, 0);
} else {
 x_423 = x_422;
}
lean_ctor_set(x_423, 0, x_420);
lean_ctor_set(x_423, 1, x_421);
return x_423;
}
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
lean_dec(x_407);
lean_dec(x_405);
lean_dec(x_402);
lean_dec(x_401);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_424 = lean_ctor_get(x_408, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_408, 1);
lean_inc(x_425);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 x_426 = x_408;
} else {
 lean_dec_ref(x_408);
 x_426 = lean_box(0);
}
if (lean_is_scalar(x_426)) {
 x_427 = lean_alloc_ctor(1, 2, 0);
} else {
 x_427 = x_426;
}
lean_ctor_set(x_427, 0, x_424);
lean_ctor_set(x_427, 1, x_425);
return x_427;
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_402);
lean_dec(x_401);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_428 = lean_ctor_get(x_404, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_404, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_430 = x_404;
} else {
 lean_dec_ref(x_404);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 2, 0);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_428);
lean_ctor_set(x_431, 1, x_429);
return x_431;
}
}
}
case 4:
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; size_t x_437; size_t x_438; lean_object* x_439; 
x_432 = lean_ctor_get(x_2, 0);
lean_inc(x_432);
lean_dec(x_2);
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 2);
lean_inc(x_434);
x_435 = lean_ctor_get(x_432, 3);
lean_inc(x_435);
lean_dec(x_432);
x_436 = lean_array_get_size(x_435);
x_437 = lean_usize_of_nat(x_436);
lean_dec(x_436);
x_438 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_439 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__6(x_1, x_437, x_438, x_435, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; uint8_t x_442; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
lean_dec(x_439);
x_442 = l_Array_isEmpty___rarg(x_440);
if (x_442 == 0)
{
lean_object* x_443; lean_object* x_444; 
x_443 = lean_box(0);
x_444 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__2(x_440, x_433, x_434, x_443, x_3, x_4, x_5, x_6, x_7, x_441);
lean_dec(x_3);
return x_444;
}
else
{
lean_object* x_445; lean_object* x_446; uint8_t x_447; 
lean_dec(x_440);
lean_dec(x_434);
lean_dec(x_433);
x_445 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9;
x_446 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7(x_445, x_3, x_4, x_5, x_6, x_7, x_441);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_447 = !lean_is_exclusive(x_446);
if (x_447 == 0)
{
return x_446;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_448 = lean_ctor_get(x_446, 0);
x_449 = lean_ctor_get(x_446, 1);
lean_inc(x_449);
lean_inc(x_448);
lean_dec(x_446);
x_450 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
return x_450;
}
}
}
else
{
uint8_t x_451; 
lean_dec(x_434);
lean_dec(x_433);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_451 = !lean_is_exclusive(x_439);
if (x_451 == 0)
{
return x_439;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_452 = lean_ctor_get(x_439, 0);
x_453 = lean_ctor_get(x_439, 1);
lean_inc(x_453);
lean_inc(x_452);
lean_dec(x_439);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_453);
return x_454;
}
}
}
case 5:
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_455 = lean_ctor_get(x_2, 0);
lean_inc(x_455);
lean_dec(x_2);
x_456 = lean_ctor_get(x_1, 0);
lean_inc(x_456);
lean_dec(x_1);
x_457 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_457, 0, x_455);
x_458 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5;
x_459 = lean_array_push(x_458, x_457);
x_460 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_460, 0, x_456);
lean_ctor_set(x_460, 1, x_459);
x_461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_8);
return x_461;
}
default: 
{
lean_object* x_462; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_462 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_462, 0, x_2);
lean_ctor_set(x_462, 1, x_8);
return x_462;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_del___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_erase___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__4(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__5(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__6(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_dec(x_5);
lean_dec(x_1);
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
x_16 = l_Lean_Compiler_LCNF_AltCore_getCode(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
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
lean_dec(x_5);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts___spec__1(x_1, x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Compiler_LCNF_ToLCNF_bindCases___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Lean_RBNode_fold___at_Lean_Compiler_LCNF_ToLCNF_bindCases___spec__1(x_1, x_3);
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
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = lean_box(0);
x_14 = lean_st_mk_ref(x_13, x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_15);
lean_inc(x_1);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(x_1, x_11, x_15, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_15, x_19);
lean_dec(x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_18);
x_23 = l_Lean_Compiler_LCNF_mkCasesResultType(x_18, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_2, 3, x_18);
lean_ctor_set(x_2, 1, x_25);
x_26 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_26, 0, x_2);
x_27 = l_Lean_RBNode_fold___at_Lean_Compiler_LCNF_ToLCNF_bindCases___spec__1(x_26, x_21);
lean_dec(x_21);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
lean_ctor_set(x_2, 3, x_18);
lean_ctor_set(x_2, 1, x_29);
x_31 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_31, 0, x_2);
x_32 = l_Lean_RBNode_fold___at_Lean_Compiler_LCNF_ToLCNF_bindCases___spec__1(x_31, x_21);
lean_dec(x_21);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_21);
lean_dec(x_18);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_23);
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
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 2);
x_45 = lean_ctor_get(x_2, 3);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_2);
x_46 = lean_box(0);
x_47 = lean_st_mk_ref(x_46, x_7);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_48);
lean_inc(x_1);
x_50 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(x_1, x_45, x_48, x_3, x_4, x_5, x_6, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_st_ref_get(x_48, x_52);
lean_dec(x_48);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_51);
x_56 = l_Lean_Compiler_LCNF_mkCasesResultType(x_51, x_3, x_4, x_5, x_6, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_43);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_44);
lean_ctor_set(x_60, 3, x_51);
x_61 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l_Lean_RBNode_fold___at_Lean_Compiler_LCNF_ToLCNF_bindCases___spec__1(x_61, x_54);
lean_dec(x_54);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_62);
if (lean_is_scalar(x_59)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_59;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_58);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_1);
x_65 = lean_ctor_get(x_56, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_56, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_67 = x_56;
} else {
 lean_dec_ref(x_56);
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
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_69 = lean_ctor_get(x_50, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_50, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_71 = x_50;
} else {
 lean_dec_ref(x_50);
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
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Compiler_LCNF_ToLCNF_bindCases___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_fold___at_Lean_Compiler_LCNF_ToLCNF_bindCases___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_array_uget(x_1, x_2);
switch (lean_obj_tag(x_11)) {
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Compiler_LCNF_eraseLetDecl(x_12, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_14;
x_9 = x_15;
goto _start;
}
case 3:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Compiler_LCNF_eraseCode(x_20, x_5, x_6, x_7, x_8, x_9);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = lean_usize_add(x_2, x_24);
x_2 = x_25;
x_4 = x_22;
x_9 = x_23;
goto _start;
}
case 4:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_27 = lean_ctor_get(x_11, 0);
lean_inc(x_27);
lean_dec(x_11);
x_28 = l_Lean_Compiler_LCNF_eraseParam(x_27, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = 1;
x_32 = lean_usize_add(x_2, x_31);
x_2 = x_32;
x_4 = x_29;
x_9 = x_30;
goto _start;
}
default: 
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; 
x_34 = lean_ctor_get(x_11, 0);
lean_inc(x_34);
lean_dec(x_11);
x_35 = 1;
x_36 = l_Lean_Compiler_LCNF_eraseFunDecl(x_34, x_35, x_5, x_6, x_7, x_8, x_9);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = 1;
x_40 = lean_usize_add(x_2, x_39);
x_2 = x_40;
x_4 = x_37;
x_9 = x_38;
goto _start;
}
}
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_9);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_63; uint8_t x_64; 
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_nat_dec_lt(x_63, x_2);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_3);
lean_ctor_set(x_65, 1, x_8);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_142; uint8_t x_143; 
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_sub(x_2, x_66);
x_142 = lean_array_get_size(x_1);
x_143 = lean_nat_dec_lt(x_67, x_142);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement;
x_145 = l___private_Init_Util_0__outOfBounds___rarg(x_144);
switch (lean_obj_tag(x_145)) {
case 0:
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_2);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_3);
x_2 = x_67;
x_3 = x_147;
goto _start;
}
case 1:
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_2);
x_149 = lean_ctor_get(x_145, 0);
lean_inc(x_149);
lean_dec(x_145);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_3);
x_2 = x_67;
x_3 = x_150;
goto _start;
}
case 2:
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_2);
x_152 = lean_ctor_get(x_145, 0);
lean_inc(x_152);
lean_dec(x_145);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_3);
x_2 = x_67;
x_3 = x_153;
goto _start;
}
case 3:
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_2);
x_155 = lean_ctor_get(x_145, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_145, 1);
lean_inc(x_156);
lean_dec(x_145);
x_68 = x_155;
x_69 = x_156;
goto block_141;
}
default: 
{
lean_object* x_157; 
lean_dec(x_145);
lean_dec(x_67);
x_157 = lean_box(0);
x_9 = x_157;
goto block_62;
}
}
}
else
{
lean_object* x_158; 
x_158 = lean_array_fget(x_1, x_67);
switch (lean_obj_tag(x_158)) {
case 0:
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_2);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_dec(x_158);
x_160 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_3);
x_2 = x_67;
x_3 = x_160;
goto _start;
}
case 1:
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_2);
x_162 = lean_ctor_get(x_158, 0);
lean_inc(x_162);
lean_dec(x_158);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_3);
x_2 = x_67;
x_3 = x_163;
goto _start;
}
case 2:
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_2);
x_165 = lean_ctor_get(x_158, 0);
lean_inc(x_165);
lean_dec(x_158);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_3);
x_2 = x_67;
x_3 = x_166;
goto _start;
}
case 3:
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_2);
x_168 = lean_ctor_get(x_158, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_158, 1);
lean_inc(x_169);
lean_dec(x_158);
x_68 = x_168;
x_69 = x_169;
goto block_141;
}
default: 
{
lean_object* x_170; 
lean_dec(x_158);
lean_dec(x_67);
x_170 = lean_box(0);
x_9 = x_170;
goto block_62;
}
}
}
block_141:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_3, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
x_72 = lean_name_eq(x_71, x_70);
lean_dec(x_70);
lean_dec(x_71);
if (x_72 == 0)
{
lean_dec(x_69);
lean_dec(x_68);
x_2 = x_67;
goto _start;
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_3);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_3, 0);
lean_dec(x_75);
x_76 = l_Lean_Compiler_LCNF_eraseParam(x_68, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_68);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
lean_ctor_set_tag(x_3, 4);
lean_ctor_set(x_3, 0, x_69);
x_2 = x_67;
x_8 = x_77;
goto _start;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_3);
x_79 = l_Lean_Compiler_LCNF_eraseParam(x_68, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_68);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_81, 0, x_69);
x_2 = x_67;
x_3 = x_81;
x_8 = x_80;
goto _start;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_68, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_68, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_68, 2);
lean_inc(x_85);
lean_inc(x_85);
x_86 = l_Lean_Expr_headBeta(x_85);
x_87 = l_Lean_Expr_isForall(x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
x_88 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_89 = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(x_68, x_3, x_88, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_92 = l_Lean_Compiler_LCNF_ToLCNF_bindCases(x_90, x_69, x_4, x_5, x_6, x_7, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_2 = x_67;
x_3 = x_93;
x_8 = x_94;
goto _start;
}
else
{
uint8_t x_96; 
lean_dec(x_67);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_92);
if (x_96 == 0)
{
return x_92;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_92, 0);
x_98 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_92);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_89);
if (x_100 == 0)
{
return x_89;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_89, 0);
x_102 = lean_ctor_get(x_89, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_89);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_104 = l_Lean_Compiler_LCNF_eraseParam(x_68, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_68);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_106, 0, x_69);
x_107 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_83);
lean_ctor_set(x_108, 1, x_84);
lean_ctor_set(x_108, 2, x_107);
lean_ctor_set(x_108, 3, x_85);
lean_ctor_set(x_108, 4, x_106);
x_109 = lean_st_ref_take(x_5, x_105);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = !lean_is_exclusive(x_110);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_108);
x_114 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_113, x_108);
lean_ctor_set(x_110, 0, x_114);
x_115 = lean_st_ref_set(x_5, x_110, x_111);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_117 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_108, x_4, x_5, x_6, x_7, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_3);
x_2 = x_67;
x_3 = x_120;
x_8 = x_119;
goto _start;
}
else
{
uint8_t x_122; 
lean_dec(x_67);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_117);
if (x_122 == 0)
{
return x_117;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_117, 0);
x_124 = lean_ctor_get(x_117, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_117);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_126 = lean_ctor_get(x_110, 0);
x_127 = lean_ctor_get(x_110, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_110);
lean_inc(x_108);
x_128 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_126, x_108);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
x_130 = lean_st_ref_set(x_5, x_129, x_111);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_132 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_108, x_4, x_5, x_6, x_7, x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_3);
x_2 = x_67;
x_3 = x_135;
x_8 = x_134;
goto _start;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_67);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_137 = lean_ctor_get(x_132, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_132, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_139 = x_132;
} else {
 lean_dec_ref(x_132);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
}
}
}
block_62:
{
lean_object* x_10; 
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Compiler_LCNF_Code_inferType(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_LCNF_eraseCode(x_3, x_4, x_5, x_6, x_7, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_toSubarray___rarg(x_1, x_17, x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 2);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_array_get_size(x_19);
x_25 = lean_nat_dec_le(x_21, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_13, 0, x_26);
return x_13;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_free_object(x_13);
x_27 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_28 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_29 = lean_box(0);
x_30 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___spec__1(x_19, x_27, x_28, x_29, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_35, 0, x_11);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_dec(x_13);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Array_toSubarray___rarg(x_1, x_38, x_2);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 2);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_nat_dec_lt(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_44 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_44, 0, x_11);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_37);
return x_45;
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_array_get_size(x_40);
x_47 = lean_nat_dec_le(x_42, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_48 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_48, 0, x_11);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_37);
return x_49;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_51 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_52 = lean_box(0);
x_53 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___spec__1(x_40, x_50, x_51, x_52, x_4, x_5, x_6, x_7, x_37);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_40);
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
x_56 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_56, 0, x_11);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_10);
if (x_58 == 0)
{
return x_10;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_10, 0);
x_60 = lean_ctor_get(x_10, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_10);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__4() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__3;
x_3 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__2;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_cache___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_cache___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_State_cache___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_seq___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_toAny___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, 1, x_1);
lean_ctor_set_uint8(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, 4, x_1);
lean_ctor_set_uint8(x_5, 5, x_2);
lean_ctor_set_uint8(x_5, 6, x_2);
lean_ctor_set_uint8(x_5, 7, x_1);
lean_ctor_set_uint8(x_5, 8, x_2);
lean_ctor_set_uint8(x_5, 9, x_3);
lean_ctor_set_uint8(x_5, 10, x_1);
lean_ctor_set_uint8(x_5, 11, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instBEqLocalInstance___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__5;
x_2 = lean_alloc_closure((void*)(l_Array_instBEqArray___rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__6;
x_2 = l_Lean_Expr_instBEqExpr;
x_3 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instHashableLocalInstance___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__8;
x_2 = lean_alloc_closure((void*)(l_instHashableArray___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__9;
x_2 = l_Lean_Expr_instHashableExpr;
x_3 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instHashableExpr;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__14;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__2;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__4;
x_3 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__11;
x_4 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__15;
x_5 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__6;
x_3 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__16;
x_4 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__4;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_st_ref_get(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
x_14 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set(x_16, 5, x_12);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__17;
x_18 = lean_st_mk_ref(x_17, x_10);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_19);
x_21 = lean_apply_5(x_1, x_16, x_19, x_5, x_6, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_get(x_19, x_23);
lean_dec(x_19);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_19);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_9, 4);
x_13 = lean_array_push(x_12, x_1);
lean_ctor_set(x_9, 4, x_13);
x_14 = lean_st_ref_set(x_2, x_9, x_10);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
x_23 = lean_ctor_get(x_9, 2);
x_24 = lean_ctor_get(x_9, 3);
x_25 = lean_ctor_get(x_9, 4);
x_26 = lean_ctor_get(x_9, 5);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_27 = lean_array_push(x_25, x_1);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_28, 2, x_23);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_28, 4, x_27);
lean_ctor_set(x_28, 5, x_26);
x_29 = lean_st_ref_set(x_2, x_28, x_10);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
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
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = 0;
x_9 = l_Lean_Compiler_LCNF_mkAuxParam(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_pushElement(x_12, x_2, x_3, x_4, x_5, x_6, x_11);
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
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
x_14 = l_Lean_Compiler_LCNF_mkFreshBinderName(x_2, x_4, x_5, x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_17 = l_Lean_Compiler_LCNF_LetValue_inferType(x_1, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Compiler_LCNF_mkLetDecl(x_15, x_18, x_1, x_4, x_5, x_6, x_7, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_21);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_21);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_pushElement(x_23, x_3, x_4, x_5, x_6, x_7, x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
lean_object* x_35; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_9);
lean_ctor_set(x_35, 1, x_8);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = l_Lean_Compiler_LCNF_mkFreshBinderName(x_2, x_4, x_5, x_6, x_7, x_8);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_39 = l_Lean_Compiler_LCNF_LetValue_inferType(x_1, x_4, x_5, x_6, x_7, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Compiler_LCNF_mkLetDecl(x_37, x_40, x_1, x_4, x_5, x_6, x_7, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_43);
x_45 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_45, 0, x_43);
x_46 = l_Lean_Compiler_LCNF_ToLCNF_pushElement(x_45, x_3, x_4, x_5, x_6, x_7, x_44);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_43, 0);
lean_inc(x_49);
lean_dec(x_43);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
lean_dec(x_43);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_37);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_39);
if (x_53 == 0)
{
return x_39;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_39, 0);
x_55 = lean_ctor_get(x_39, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_39);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
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
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_st_ref_get(x_2, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 4);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
x_13 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_13, 0, x_8);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode(x_12, x_13, x_3, x_4, x_5, x_6, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_box(1);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_2, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 4);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_24, 0, x_18);
x_25 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode(x_23, x_24, x_3, x_4, x_5, x_6, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toCode(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__5;
x_3 = l_Lean_Compiler_LCNF_ToLCNF_State_cache___default___closed__1;
x_4 = l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__1;
x_5 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_6 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set(x_6, 5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__2;
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
uint8_t x_19; 
lean_dec(x_9);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_run___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = 0;
return x_3;
}
case 3:
{
uint8_t x_4; 
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_10);
lean_dec(x_1);
x_11 = 0;
return x_11;
}
case 4:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_environment_find(x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = 2;
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 5)
{
uint8_t x_16; 
lean_dec(x_15);
x_16 = 0;
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_15);
x_17 = 2;
return x_17;
}
}
}
default: 
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_1);
x_18 = 2;
return x_18;
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
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__2(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = lean_hashmap_mk_idx(x_6, x_7);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Expr_hash(x_12);
x_17 = lean_hashmap_mk_idx(x_15, x_16);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_AssocList_foldlM___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__5(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_HashMapImp_moveEntries___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
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
x_9 = lean_expr_eqv(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
x_11 = lean_box(x_2);
lean_ctor_set(x_3, 1, x_11);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_15 = lean_expr_eqv(x_12, x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6(x_1, x_2, x_14);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_12);
x_18 = lean_box(x_2);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_14);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
lean_inc(x_7);
x_9 = lean_hashmap_mk_idx(x_7, x_8);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Lean_AssocList_contains___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__2(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_box(x_3);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_10);
x_16 = lean_array_uset(x_6, x_9, x_15);
x_17 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_13);
x_18 = lean_nat_dec_le(x_17, x_7);
lean_dec(x_7);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_Lean_HashMapImp_expand___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__3(x_13, x_16);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_Lean_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6(x_2, x_3, x_10);
x_21 = lean_array_uset(x_6, x_9, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = l_Lean_Expr_hash(x_2);
lean_inc(x_24);
x_26 = lean_hashmap_mk_idx(x_24, x_25);
x_27 = lean_array_uget(x_23, x_26);
x_28 = l_Lean_AssocList_contains___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__2(x_2, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_22, x_29);
lean_dec(x_22);
x_31 = lean_box(x_3);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_27);
x_33 = lean_array_uset(x_23, x_26, x_32);
x_34 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_30);
x_35 = lean_nat_dec_le(x_34, x_24);
lean_dec(x_24);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_HashMapImp_expand___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__3(x_30, x_33);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_Lean_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6(x_2, x_3, x_27);
x_39 = lean_array_uset(x_23, x_26, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__8(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_hashmap_mk_idx(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__8(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
x_15 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_16);
lean_ctor_set(x_17, 5, x_13);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__17;
x_19 = lean_st_mk_ref(x_18, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_20);
lean_inc(x_1);
x_22 = l_Lean_Meta_isTypeFormerType(x_1, x_17, x_20, x_6, x_7, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_20, x_24);
lean_dec(x_20);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_take(x_3, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_28, 3);
x_32 = lean_unbox(x_23);
x_33 = l_Lean_HashMap_insert___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__1(x_31, x_1, x_32);
lean_ctor_set(x_28, 3, x_33);
x_34 = lean_st_ref_set(x_3, x_28, x_29);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_23);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_39 = lean_ctor_get(x_28, 0);
x_40 = lean_ctor_get(x_28, 1);
x_41 = lean_ctor_get(x_28, 2);
x_42 = lean_ctor_get(x_28, 3);
x_43 = lean_ctor_get(x_28, 4);
x_44 = lean_ctor_get(x_28, 5);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_28);
x_45 = lean_unbox(x_23);
x_46 = l_Lean_HashMap_insert___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__1(x_42, x_1, x_45);
x_47 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_40);
lean_ctor_set(x_47, 2, x_41);
lean_ctor_set(x_47, 3, x_46);
lean_ctor_set(x_47, 4, x_43);
lean_ctor_set(x_47, 5, x_44);
x_48 = lean_st_ref_set(x_3, x_47, x_29);
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
lean_ctor_set(x_51, 0, x_23);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_20);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_22);
if (x_52 == 0)
{
return x_22;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_22, 0);
x_54 = lean_ctor_get(x_22, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_22);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(x_12, x_1);
switch (x_13) {
case 0:
{
uint8_t x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
case 1:
{
uint8_t x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = 1;
x_17 = lean_box(x_16);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
default: 
{
lean_object* x_18; uint8_t x_19; 
lean_free_object(x_8);
x_18 = lean_st_ref_get(x_2, x_11);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_20, 3);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_1);
x_23 = l_Lean_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__7(x_22, x_1);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_18);
x_24 = lean_box(0);
x_25 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1(x_1, x_24, x_2, x_3, x_4, x_5, x_6, x_21);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_18, 0, x_26);
return x_18;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_ctor_get(x_27, 3);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_1);
x_30 = l_Lean_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__7(x_29, x_1);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1(x_1, x_31, x_2, x_3, x_4, x_5, x_6, x_28);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_8, 0);
x_36 = lean_ctor_get(x_8, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_8);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(x_37, x_1);
switch (x_38) {
case 0:
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = 0;
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
case 1:
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = 1;
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_36);
return x_44;
}
default: 
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_st_ref_get(x_2, x_36);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_46, 3);
lean_inc(x_49);
lean_dec(x_46);
lean_inc(x_1);
x_50 = l_Lean_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__7(x_49, x_1);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_48);
x_51 = lean_box(0);
x_52 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1(x_1, x_51, x_2, x_3, x_4, x_5, x_6, x_47);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
lean_dec(x_50);
if (lean_is_scalar(x_48)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_48;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_47);
return x_54;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_HashMap_insert___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__1(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__8(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_8 = lean_st_ref_get(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 5);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_st_ref_take(x_2, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_16, 4);
lean_dec(x_19);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
lean_ctor_set(x_16, 4, x_20);
x_21 = lean_st_ref_set(x_2, x_16, x_17);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_2);
x_23 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_2, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_2, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_27, 2);
lean_inc(x_32);
lean_dec(x_27);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_30, 5);
lean_dec(x_34);
x_35 = lean_ctor_get(x_30, 4);
lean_dec(x_35);
x_36 = lean_ctor_get(x_30, 2);
lean_dec(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_30, 0);
lean_dec(x_38);
lean_ctor_set(x_30, 5, x_14);
lean_ctor_set(x_30, 4, x_13);
lean_ctor_set(x_30, 2, x_32);
lean_ctor_set(x_30, 1, x_12);
lean_ctor_set(x_30, 0, x_11);
x_39 = lean_st_ref_set(x_2, x_30, x_31);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_24);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_24);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_30, 3);
lean_inc(x_44);
lean_dec(x_30);
x_45 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_45, 0, x_11);
lean_ctor_set(x_45, 1, x_12);
lean_ctor_set(x_45, 2, x_32);
lean_ctor_set(x_45, 3, x_44);
lean_ctor_set(x_45, 4, x_13);
lean_ctor_set(x_45, 5, x_14);
x_46 = lean_st_ref_set(x_2, x_45, x_31);
lean_dec(x_2);
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
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_24);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_50 = lean_ctor_get(x_23, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_23, 1);
lean_inc(x_51);
lean_dec(x_23);
x_52 = lean_st_ref_get(x_2, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_st_ref_get(x_2, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_53, 2);
lean_inc(x_58);
lean_dec(x_53);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_60 = lean_ctor_get(x_56, 5);
lean_dec(x_60);
x_61 = lean_ctor_get(x_56, 4);
lean_dec(x_61);
x_62 = lean_ctor_get(x_56, 2);
lean_dec(x_62);
x_63 = lean_ctor_get(x_56, 1);
lean_dec(x_63);
x_64 = lean_ctor_get(x_56, 0);
lean_dec(x_64);
lean_ctor_set(x_56, 5, x_14);
lean_ctor_set(x_56, 4, x_13);
lean_ctor_set(x_56, 2, x_58);
lean_ctor_set(x_56, 1, x_12);
lean_ctor_set(x_56, 0, x_11);
x_65 = lean_st_ref_set(x_2, x_56, x_57);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
lean_ctor_set_tag(x_65, 1);
lean_ctor_set(x_65, 0, x_50);
return x_65;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_50);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_56, 3);
lean_inc(x_70);
lean_dec(x_56);
x_71 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_71, 0, x_11);
lean_ctor_set(x_71, 1, x_12);
lean_ctor_set(x_71, 2, x_58);
lean_ctor_set(x_71, 3, x_70);
lean_ctor_set(x_71, 4, x_13);
lean_ctor_set(x_71, 5, x_14);
x_72 = lean_st_ref_set(x_2, x_71, x_57);
lean_dec(x_2);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
 lean_ctor_set_tag(x_75, 1);
}
lean_ctor_set(x_75, 0, x_50);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_76 = lean_ctor_get(x_16, 0);
x_77 = lean_ctor_get(x_16, 1);
x_78 = lean_ctor_get(x_16, 2);
x_79 = lean_ctor_get(x_16, 3);
x_80 = lean_ctor_get(x_16, 5);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_16);
x_81 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_82 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_82, 0, x_76);
lean_ctor_set(x_82, 1, x_77);
lean_ctor_set(x_82, 2, x_78);
lean_ctor_set(x_82, 3, x_79);
lean_ctor_set(x_82, 4, x_81);
lean_ctor_set(x_82, 5, x_80);
x_83 = lean_st_ref_set(x_2, x_82, x_17);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
lean_inc(x_2);
x_85 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_st_ref_get(x_2, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_st_ref_get(x_2, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_89, 2);
lean_inc(x_94);
lean_dec(x_89);
x_95 = lean_ctor_get(x_92, 3);
lean_inc(x_95);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 lean_ctor_release(x_92, 2);
 lean_ctor_release(x_92, 3);
 lean_ctor_release(x_92, 4);
 lean_ctor_release(x_92, 5);
 x_96 = x_92;
} else {
 lean_dec_ref(x_92);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 6, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_11);
lean_ctor_set(x_97, 1, x_12);
lean_ctor_set(x_97, 2, x_94);
lean_ctor_set(x_97, 3, x_95);
lean_ctor_set(x_97, 4, x_13);
lean_ctor_set(x_97, 5, x_14);
x_98 = lean_st_ref_set(x_2, x_97, x_93);
lean_dec(x_2);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_86);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_102 = lean_ctor_get(x_85, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_85, 1);
lean_inc(x_103);
lean_dec(x_85);
x_104 = lean_st_ref_get(x_2, x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_st_ref_get(x_2, x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_105, 2);
lean_inc(x_110);
lean_dec(x_105);
x_111 = lean_ctor_get(x_108, 3);
lean_inc(x_111);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 lean_ctor_release(x_108, 2);
 lean_ctor_release(x_108, 3);
 lean_ctor_release(x_108, 4);
 lean_ctor_release(x_108, 5);
 x_112 = x_108;
} else {
 lean_dec_ref(x_108);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(0, 6, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_11);
lean_ctor_set(x_113, 1, x_12);
lean_ctor_set(x_113, 2, x_110);
lean_ctor_set(x_113, 3, x_111);
lean_ctor_set(x_113, 4, x_13);
lean_ctor_set(x_113, 5, x_14);
x_114 = lean_st_ref_set(x_2, x_113, x_109);
lean_dec(x_2);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
 lean_ctor_set_tag(x_117, 1);
}
lean_ctor_set(x_117, 0, x_102);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_withNewScope___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_LCNF_ToLCNF_applyToAny___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_235; size_t x_236; size_t x_237; size_t x_238; lean_object* x_239; size_t x_240; uint8_t x_241; 
x_235 = lean_ctor_get(x_3, 0);
lean_inc(x_235);
x_236 = lean_ptr_addr(x_2);
x_237 = lean_ctor_get_usize(x_3, 1);
x_238 = lean_usize_mod(x_236, x_237);
x_239 = lean_array_uget(x_235, x_238);
x_240 = lean_ptr_addr(x_239);
lean_dec(x_239);
x_241 = lean_usize_dec_eq(x_236, x_240);
if (x_241 == 0)
{
lean_dec(x_235);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_2, 0);
lean_inc(x_242);
x_243 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_1, x_242);
lean_dec(x_242);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; 
x_244 = lean_box(0);
x_4 = x_244;
goto block_234;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_243);
x_245 = l_Lean_Compiler_LCNF_erasedExpr;
x_246 = l_Lean_Expr_ReplaceImpl_Cache_store(x_3, x_2, x_245);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
return x_247;
}
}
else
{
lean_object* x_248; 
x_248 = lean_box(0);
x_4 = x_248;
goto block_234;
}
}
else
{
size_t x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_2);
x_249 = lean_usize_add(x_238, x_237);
x_250 = lean_array_uget(x_235, x_249);
lean_dec(x_235);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_3);
return x_251;
}
block_234:
{
lean_dec(x_4);
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_inc(x_5);
x_7 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_LCNF_ToLCNF_applyToAny___spec__1(x_1, x_5, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_6);
x_10 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_LCNF_ToLCNF_applyToAny___spec__1(x_1, x_6, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_15 = lean_ptr_addr(x_8);
x_16 = lean_usize_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_17 = l_Lean_Expr_app___override(x_8, x_12);
lean_inc(x_17);
x_18 = l_Lean_Expr_ReplaceImpl_Cache_store(x_13, x_2, x_17);
lean_ctor_set(x_10, 1, x_18);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_20 = lean_ptr_addr(x_12);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Expr_app___override(x_8, x_12);
lean_inc(x_22);
x_23 = l_Lean_Expr_ReplaceImpl_Cache_store(x_13, x_2, x_22);
lean_ctor_set(x_10, 1, x_23);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
else
{
lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_8);
lean_inc_n(x_2, 2);
x_24 = l_Lean_Expr_ReplaceImpl_Cache_store(x_13, x_2, x_2);
lean_ctor_set(x_10, 1, x_24);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_28 = lean_ptr_addr(x_8);
x_29 = lean_usize_dec_eq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
x_30 = l_Lean_Expr_app___override(x_8, x_25);
lean_inc(x_30);
x_31 = l_Lean_Expr_ReplaceImpl_Cache_store(x_26, x_2, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
else
{
size_t x_33; size_t x_34; uint8_t x_35; 
x_33 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_34 = lean_ptr_addr(x_25);
x_35 = lean_usize_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = l_Lean_Expr_app___override(x_8, x_25);
lean_inc(x_36);
x_37 = l_Lean_Expr_ReplaceImpl_Cache_store(x_26, x_2, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_25);
lean_dec(x_8);
lean_inc_n(x_2, 2);
x_39 = l_Lean_Expr_ReplaceImpl_Cache_store(x_26, x_2, x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_2);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
case 6:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 2);
lean_inc(x_43);
x_44 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_42);
x_45 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_LCNF_ToLCNF_applyToAny___spec__1(x_1, x_42, x_3);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_43);
x_48 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_LCNF_ToLCNF_applyToAny___spec__1(x_1, x_43, x_47);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
x_52 = l_Lean_Expr_lam___override(x_41, x_42, x_43, x_44);
x_53 = lean_ptr_addr(x_42);
lean_dec(x_42);
x_54 = lean_ptr_addr(x_46);
x_55 = lean_usize_dec_eq(x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_52);
lean_dec(x_43);
x_56 = l_Lean_Expr_lam___override(x_41, x_46, x_50, x_44);
lean_inc(x_56);
x_57 = l_Lean_Expr_ReplaceImpl_Cache_store(x_51, x_2, x_56);
lean_ctor_set(x_48, 1, x_57);
lean_ctor_set(x_48, 0, x_56);
return x_48;
}
else
{
size_t x_58; size_t x_59; uint8_t x_60; 
x_58 = lean_ptr_addr(x_43);
lean_dec(x_43);
x_59 = lean_ptr_addr(x_50);
x_60 = lean_usize_dec_eq(x_58, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_52);
x_61 = l_Lean_Expr_lam___override(x_41, x_46, x_50, x_44);
lean_inc(x_61);
x_62 = l_Lean_Expr_ReplaceImpl_Cache_store(x_51, x_2, x_61);
lean_ctor_set(x_48, 1, x_62);
lean_ctor_set(x_48, 0, x_61);
return x_48;
}
else
{
uint8_t x_63; 
x_63 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_44, x_44);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_52);
x_64 = l_Lean_Expr_lam___override(x_41, x_46, x_50, x_44);
lean_inc(x_64);
x_65 = l_Lean_Expr_ReplaceImpl_Cache_store(x_51, x_2, x_64);
lean_ctor_set(x_48, 1, x_65);
lean_ctor_set(x_48, 0, x_64);
return x_48;
}
else
{
lean_object* x_66; 
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_41);
lean_inc(x_52);
x_66 = l_Lean_Expr_ReplaceImpl_Cache_store(x_51, x_2, x_52);
lean_ctor_set(x_48, 1, x_66);
lean_ctor_set(x_48, 0, x_52);
return x_48;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; uint8_t x_72; 
x_67 = lean_ctor_get(x_48, 0);
x_68 = lean_ctor_get(x_48, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_48);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
x_69 = l_Lean_Expr_lam___override(x_41, x_42, x_43, x_44);
x_70 = lean_ptr_addr(x_42);
lean_dec(x_42);
x_71 = lean_ptr_addr(x_46);
x_72 = lean_usize_dec_eq(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_69);
lean_dec(x_43);
x_73 = l_Lean_Expr_lam___override(x_41, x_46, x_67, x_44);
lean_inc(x_73);
x_74 = l_Lean_Expr_ReplaceImpl_Cache_store(x_68, x_2, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
else
{
size_t x_76; size_t x_77; uint8_t x_78; 
x_76 = lean_ptr_addr(x_43);
lean_dec(x_43);
x_77 = lean_ptr_addr(x_67);
x_78 = lean_usize_dec_eq(x_76, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_69);
x_79 = l_Lean_Expr_lam___override(x_41, x_46, x_67, x_44);
lean_inc(x_79);
x_80 = l_Lean_Expr_ReplaceImpl_Cache_store(x_68, x_2, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
else
{
uint8_t x_82; 
x_82 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_44, x_44);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_69);
x_83 = l_Lean_Expr_lam___override(x_41, x_46, x_67, x_44);
lean_inc(x_83);
x_84 = l_Lean_Expr_ReplaceImpl_Cache_store(x_68, x_2, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_67);
lean_dec(x_46);
lean_dec(x_41);
lean_inc(x_69);
x_86 = l_Lean_Expr_ReplaceImpl_Cache_store(x_68, x_2, x_69);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_69);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
}
case 7:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_88 = lean_ctor_get(x_2, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_2, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_2, 2);
lean_inc(x_90);
x_91 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_89);
x_92 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_LCNF_ToLCNF_applyToAny___spec__1(x_1, x_89, x_3);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_inc(x_90);
x_95 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_LCNF_ToLCNF_applyToAny___spec__1(x_1, x_90, x_94);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; size_t x_100; size_t x_101; uint8_t x_102; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
x_99 = l_Lean_Expr_forallE___override(x_88, x_89, x_90, x_91);
x_100 = lean_ptr_addr(x_89);
lean_dec(x_89);
x_101 = lean_ptr_addr(x_93);
x_102 = lean_usize_dec_eq(x_100, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_99);
lean_dec(x_90);
x_103 = l_Lean_Expr_forallE___override(x_88, x_93, x_97, x_91);
lean_inc(x_103);
x_104 = l_Lean_Expr_ReplaceImpl_Cache_store(x_98, x_2, x_103);
lean_ctor_set(x_95, 1, x_104);
lean_ctor_set(x_95, 0, x_103);
return x_95;
}
else
{
size_t x_105; size_t x_106; uint8_t x_107; 
x_105 = lean_ptr_addr(x_90);
lean_dec(x_90);
x_106 = lean_ptr_addr(x_97);
x_107 = lean_usize_dec_eq(x_105, x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_99);
x_108 = l_Lean_Expr_forallE___override(x_88, x_93, x_97, x_91);
lean_inc(x_108);
x_109 = l_Lean_Expr_ReplaceImpl_Cache_store(x_98, x_2, x_108);
lean_ctor_set(x_95, 1, x_109);
lean_ctor_set(x_95, 0, x_108);
return x_95;
}
else
{
uint8_t x_110; 
x_110 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_91, x_91);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_99);
x_111 = l_Lean_Expr_forallE___override(x_88, x_93, x_97, x_91);
lean_inc(x_111);
x_112 = l_Lean_Expr_ReplaceImpl_Cache_store(x_98, x_2, x_111);
lean_ctor_set(x_95, 1, x_112);
lean_ctor_set(x_95, 0, x_111);
return x_95;
}
else
{
lean_object* x_113; 
lean_dec(x_97);
lean_dec(x_93);
lean_dec(x_88);
lean_inc(x_99);
x_113 = l_Lean_Expr_ReplaceImpl_Cache_store(x_98, x_2, x_99);
lean_ctor_set(x_95, 1, x_113);
lean_ctor_set(x_95, 0, x_99);
return x_95;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; size_t x_117; size_t x_118; uint8_t x_119; 
x_114 = lean_ctor_get(x_95, 0);
x_115 = lean_ctor_get(x_95, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_95);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
x_116 = l_Lean_Expr_forallE___override(x_88, x_89, x_90, x_91);
x_117 = lean_ptr_addr(x_89);
lean_dec(x_89);
x_118 = lean_ptr_addr(x_93);
x_119 = lean_usize_dec_eq(x_117, x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_116);
lean_dec(x_90);
x_120 = l_Lean_Expr_forallE___override(x_88, x_93, x_114, x_91);
lean_inc(x_120);
x_121 = l_Lean_Expr_ReplaceImpl_Cache_store(x_115, x_2, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
else
{
size_t x_123; size_t x_124; uint8_t x_125; 
x_123 = lean_ptr_addr(x_90);
lean_dec(x_90);
x_124 = lean_ptr_addr(x_114);
x_125 = lean_usize_dec_eq(x_123, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_116);
x_126 = l_Lean_Expr_forallE___override(x_88, x_93, x_114, x_91);
lean_inc(x_126);
x_127 = l_Lean_Expr_ReplaceImpl_Cache_store(x_115, x_2, x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
else
{
uint8_t x_129; 
x_129 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_91, x_91);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_116);
x_130 = l_Lean_Expr_forallE___override(x_88, x_93, x_114, x_91);
lean_inc(x_130);
x_131 = l_Lean_Expr_ReplaceImpl_Cache_store(x_115, x_2, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_114);
lean_dec(x_93);
lean_dec(x_88);
lean_inc(x_116);
x_133 = l_Lean_Expr_ReplaceImpl_Cache_store(x_115, x_2, x_116);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_116);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
}
case 8:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_135 = lean_ctor_get(x_2, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_2, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_2, 2);
lean_inc(x_137);
x_138 = lean_ctor_get(x_2, 3);
lean_inc(x_138);
x_139 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_136);
x_140 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_LCNF_ToLCNF_applyToAny___spec__1(x_1, x_136, x_3);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
lean_inc(x_137);
x_143 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_LCNF_ToLCNF_applyToAny___spec__1(x_1, x_137, x_142);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
lean_inc(x_138);
x_146 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_LCNF_ToLCNF_applyToAny___spec__1(x_1, x_138, x_145);
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; size_t x_150; size_t x_151; uint8_t x_152; 
x_148 = lean_ctor_get(x_146, 0);
x_149 = lean_ctor_get(x_146, 1);
x_150 = lean_ptr_addr(x_136);
lean_dec(x_136);
x_151 = lean_ptr_addr(x_141);
x_152 = lean_usize_dec_eq(x_150, x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_138);
lean_dec(x_137);
x_153 = l_Lean_Expr_letE___override(x_135, x_141, x_144, x_148, x_139);
lean_inc(x_153);
x_154 = l_Lean_Expr_ReplaceImpl_Cache_store(x_149, x_2, x_153);
lean_ctor_set(x_146, 1, x_154);
lean_ctor_set(x_146, 0, x_153);
return x_146;
}
else
{
size_t x_155; size_t x_156; uint8_t x_157; 
x_155 = lean_ptr_addr(x_137);
lean_dec(x_137);
x_156 = lean_ptr_addr(x_144);
x_157 = lean_usize_dec_eq(x_155, x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_138);
x_158 = l_Lean_Expr_letE___override(x_135, x_141, x_144, x_148, x_139);
lean_inc(x_158);
x_159 = l_Lean_Expr_ReplaceImpl_Cache_store(x_149, x_2, x_158);
lean_ctor_set(x_146, 1, x_159);
lean_ctor_set(x_146, 0, x_158);
return x_146;
}
else
{
size_t x_160; size_t x_161; uint8_t x_162; 
x_160 = lean_ptr_addr(x_138);
lean_dec(x_138);
x_161 = lean_ptr_addr(x_148);
x_162 = lean_usize_dec_eq(x_160, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = l_Lean_Expr_letE___override(x_135, x_141, x_144, x_148, x_139);
lean_inc(x_163);
x_164 = l_Lean_Expr_ReplaceImpl_Cache_store(x_149, x_2, x_163);
lean_ctor_set(x_146, 1, x_164);
lean_ctor_set(x_146, 0, x_163);
return x_146;
}
else
{
lean_object* x_165; 
lean_dec(x_148);
lean_dec(x_144);
lean_dec(x_141);
lean_dec(x_135);
lean_inc_n(x_2, 2);
x_165 = l_Lean_Expr_ReplaceImpl_Cache_store(x_149, x_2, x_2);
lean_ctor_set(x_146, 1, x_165);
lean_ctor_set(x_146, 0, x_2);
return x_146;
}
}
}
}
else
{
lean_object* x_166; lean_object* x_167; size_t x_168; size_t x_169; uint8_t x_170; 
x_166 = lean_ctor_get(x_146, 0);
x_167 = lean_ctor_get(x_146, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_146);
x_168 = lean_ptr_addr(x_136);
lean_dec(x_136);
x_169 = lean_ptr_addr(x_141);
x_170 = lean_usize_dec_eq(x_168, x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_138);
lean_dec(x_137);
x_171 = l_Lean_Expr_letE___override(x_135, x_141, x_144, x_166, x_139);
lean_inc(x_171);
x_172 = l_Lean_Expr_ReplaceImpl_Cache_store(x_167, x_2, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
else
{
size_t x_174; size_t x_175; uint8_t x_176; 
x_174 = lean_ptr_addr(x_137);
lean_dec(x_137);
x_175 = lean_ptr_addr(x_144);
x_176 = lean_usize_dec_eq(x_174, x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_138);
x_177 = l_Lean_Expr_letE___override(x_135, x_141, x_144, x_166, x_139);
lean_inc(x_177);
x_178 = l_Lean_Expr_ReplaceImpl_Cache_store(x_167, x_2, x_177);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
else
{
size_t x_180; size_t x_181; uint8_t x_182; 
x_180 = lean_ptr_addr(x_138);
lean_dec(x_138);
x_181 = lean_ptr_addr(x_166);
x_182 = lean_usize_dec_eq(x_180, x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = l_Lean_Expr_letE___override(x_135, x_141, x_144, x_166, x_139);
lean_inc(x_183);
x_184 = l_Lean_Expr_ReplaceImpl_Cache_store(x_167, x_2, x_183);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_166);
lean_dec(x_144);
lean_dec(x_141);
lean_dec(x_135);
lean_inc_n(x_2, 2);
x_186 = l_Lean_Expr_ReplaceImpl_Cache_store(x_167, x_2, x_2);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_2);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
}
}
case 10:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_188 = lean_ctor_get(x_2, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_2, 1);
lean_inc(x_189);
lean_inc(x_189);
x_190 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_LCNF_ToLCNF_applyToAny___spec__1(x_1, x_189, x_3);
x_191 = !lean_is_exclusive(x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; size_t x_194; size_t x_195; uint8_t x_196; 
x_192 = lean_ctor_get(x_190, 0);
x_193 = lean_ctor_get(x_190, 1);
x_194 = lean_ptr_addr(x_189);
lean_dec(x_189);
x_195 = lean_ptr_addr(x_192);
x_196 = lean_usize_dec_eq(x_194, x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = l_Lean_Expr_mdata___override(x_188, x_192);
lean_inc(x_197);
x_198 = l_Lean_Expr_ReplaceImpl_Cache_store(x_193, x_2, x_197);
lean_ctor_set(x_190, 1, x_198);
lean_ctor_set(x_190, 0, x_197);
return x_190;
}
else
{
lean_object* x_199; 
lean_dec(x_192);
lean_dec(x_188);
lean_inc_n(x_2, 2);
x_199 = l_Lean_Expr_ReplaceImpl_Cache_store(x_193, x_2, x_2);
lean_ctor_set(x_190, 1, x_199);
lean_ctor_set(x_190, 0, x_2);
return x_190;
}
}
else
{
lean_object* x_200; lean_object* x_201; size_t x_202; size_t x_203; uint8_t x_204; 
x_200 = lean_ctor_get(x_190, 0);
x_201 = lean_ctor_get(x_190, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_190);
x_202 = lean_ptr_addr(x_189);
lean_dec(x_189);
x_203 = lean_ptr_addr(x_200);
x_204 = lean_usize_dec_eq(x_202, x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = l_Lean_Expr_mdata___override(x_188, x_200);
lean_inc(x_205);
x_206 = l_Lean_Expr_ReplaceImpl_Cache_store(x_201, x_2, x_205);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_200);
lean_dec(x_188);
lean_inc_n(x_2, 2);
x_208 = l_Lean_Expr_ReplaceImpl_Cache_store(x_201, x_2, x_2);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_2);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
case 11:
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_210 = lean_ctor_get(x_2, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_2, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_2, 2);
lean_inc(x_212);
lean_inc(x_212);
x_213 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_LCNF_ToLCNF_applyToAny___spec__1(x_1, x_212, x_3);
x_214 = !lean_is_exclusive(x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; size_t x_217; size_t x_218; uint8_t x_219; 
x_215 = lean_ctor_get(x_213, 0);
x_216 = lean_ctor_get(x_213, 1);
x_217 = lean_ptr_addr(x_212);
lean_dec(x_212);
x_218 = lean_ptr_addr(x_215);
x_219 = lean_usize_dec_eq(x_217, x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; 
x_220 = l_Lean_Expr_proj___override(x_210, x_211, x_215);
lean_inc(x_220);
x_221 = l_Lean_Expr_ReplaceImpl_Cache_store(x_216, x_2, x_220);
lean_ctor_set(x_213, 1, x_221);
lean_ctor_set(x_213, 0, x_220);
return x_213;
}
else
{
lean_object* x_222; 
lean_dec(x_215);
lean_dec(x_211);
lean_dec(x_210);
lean_inc_n(x_2, 2);
x_222 = l_Lean_Expr_ReplaceImpl_Cache_store(x_216, x_2, x_2);
lean_ctor_set(x_213, 1, x_222);
lean_ctor_set(x_213, 0, x_2);
return x_213;
}
}
else
{
lean_object* x_223; lean_object* x_224; size_t x_225; size_t x_226; uint8_t x_227; 
x_223 = lean_ctor_get(x_213, 0);
x_224 = lean_ctor_get(x_213, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_213);
x_225 = lean_ptr_addr(x_212);
lean_dec(x_212);
x_226 = lean_ptr_addr(x_223);
x_227 = lean_usize_dec_eq(x_225, x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = l_Lean_Expr_proj___override(x_210, x_211, x_223);
lean_inc(x_228);
x_229 = l_Lean_Expr_ReplaceImpl_Cache_store(x_224, x_2, x_228);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_223);
lean_dec(x_211);
lean_dec(x_210);
lean_inc_n(x_2, 2);
x_231 = l_Lean_Expr_ReplaceImpl_Cache_store(x_224, x_2, x_2);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_2);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
default: 
{
lean_object* x_233; 
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_2);
lean_ctor_set(x_233, 1, x_3);
return x_233;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_2, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 5);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Expr_ReplaceImpl_Cache_new(x_1);
x_13 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_LCNF_ToLCNF_applyToAny___spec__1(x_11, x_1, x_12);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_ctor_get(x_15, 5);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_ReplaceImpl_Cache_new(x_1);
x_19 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_LCNF_ToLCNF_applyToAny___spec__1(x_17, x_1, x_18);
lean_dec(x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_LCNF_ToLCNF_applyToAny___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Compiler_LCNF_ToLCNF_applyToAny___spec__1(x_1, x_2, x_3);
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
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_hashmap_mk_idx(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__2(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__4(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = lean_hashmap_mk_idx(x_6, x_7);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Expr_hash(x_12);
x_17 = lean_hashmap_mk_idx(x_15, x_16);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__7(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = lean_expr_eqv(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__8(x_1, x_2, x_8);
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
x_14 = lean_expr_eqv(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__8(x_1, x_2, x_13);
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
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
lean_inc(x_7);
x_9 = lean_hashmap_mk_idx(x_7, x_8);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__4(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_13);
x_17 = lean_nat_dec_le(x_16, x_7);
lean_dec(x_7);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__5(x_13, x_15);
return x_18;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__8(x_2, x_3, x_10);
x_20 = lean_array_uset(x_6, x_9, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l_Lean_Expr_hash(x_2);
lean_inc(x_23);
x_25 = lean_hashmap_mk_idx(x_23, x_24);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__4(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_21, x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_array_uset(x_22, x_25, x_30);
x_32 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_29);
x_33 = lean_nat_dec_le(x_32, x_23);
lean_dec(x_23);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__5(x_29, x_31);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__8(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_2, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__1(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_8);
x_14 = lean_st_ref_get(x_2, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
x_20 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_18);
lean_ctor_set(x_22, 4, x_21);
lean_ctor_set(x_22, 5, x_18);
x_23 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__17;
x_24 = lean_st_mk_ref(x_23, x_16);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_25);
lean_inc(x_1);
x_27 = l_Lean_Compiler_LCNF_toLCNFType(x_1, x_22, x_25, x_5, x_6, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_st_ref_get(x_25, x_29);
lean_dec(x_25);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny(x_28, x_2, x_3, x_4, x_5, x_6, x_31);
lean_dec(x_6);
lean_dec(x_5);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_take(x_2, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_36, 2);
lean_inc(x_33);
x_40 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__3(x_39, x_1, x_33);
lean_ctor_set(x_36, 2, x_40);
x_41 = lean_st_ref_set(x_2, x_36, x_37);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_33);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_46 = lean_ctor_get(x_36, 0);
x_47 = lean_ctor_get(x_36, 1);
x_48 = lean_ctor_get(x_36, 2);
x_49 = lean_ctor_get(x_36, 3);
x_50 = lean_ctor_get(x_36, 4);
x_51 = lean_ctor_get(x_36, 5);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_36);
lean_inc(x_33);
x_52 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__3(x_48, x_1, x_33);
x_53 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_47);
lean_ctor_set(x_53, 2, x_52);
lean_ctor_set(x_53, 3, x_49);
lean_ctor_set(x_53, 4, x_50);
lean_ctor_set(x_53, 5, x_51);
x_54 = lean_st_ref_set(x_2, x_53, x_37);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_33);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_27);
if (x_58 == 0)
{
return x_27;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_27, 0);
x_60 = lean_ctor_get(x_27, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_27);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_62 = lean_ctor_get(x_13, 0);
lean_inc(x_62);
lean_dec(x_13);
lean_ctor_set(x_8, 0, x_62);
return x_8;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_8, 0);
x_64 = lean_ctor_get(x_8, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_8);
x_65 = lean_ctor_get(x_63, 2);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_1);
x_66 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__1(x_65, x_1);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_67 = lean_st_ref_get(x_2, x_64);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_box(0);
x_72 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
x_73 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_70);
lean_ctor_set(x_75, 2, x_73);
lean_ctor_set(x_75, 3, x_71);
lean_ctor_set(x_75, 4, x_74);
lean_ctor_set(x_75, 5, x_71);
x_76 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__17;
x_77 = lean_st_mk_ref(x_76, x_69);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_78);
lean_inc(x_1);
x_80 = l_Lean_Compiler_LCNF_toLCNFType(x_1, x_75, x_78, x_5, x_6, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_st_ref_get(x_78, x_82);
lean_dec(x_78);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny(x_81, x_2, x_3, x_4, x_5, x_6, x_84);
lean_dec(x_6);
lean_dec(x_5);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_st_ref_take(x_2, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_89, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_89, 3);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 4);
lean_inc(x_95);
x_96 = lean_ctor_get(x_89, 5);
lean_inc(x_96);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 lean_ctor_release(x_89, 4);
 lean_ctor_release(x_89, 5);
 x_97 = x_89;
} else {
 lean_dec_ref(x_89);
 x_97 = lean_box(0);
}
lean_inc(x_86);
x_98 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__3(x_93, x_1, x_86);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 6, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_91);
lean_ctor_set(x_99, 1, x_92);
lean_ctor_set(x_99, 2, x_98);
lean_ctor_set(x_99, 3, x_94);
lean_ctor_set(x_99, 4, x_95);
lean_ctor_set(x_99, 5, x_96);
x_100 = lean_st_ref_set(x_2, x_99, x_90);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_86);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_78);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_104 = lean_ctor_get(x_80, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_80, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_106 = x_80;
} else {
 lean_dec_ref(x_80);
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
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_108 = lean_ctor_get(x_66, 0);
lean_inc(x_108);
lean_dec(x_66);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_64);
return x_109;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Name_hasMacroScopes(x_1);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_erase_macro_scopes(x_1);
x_10 = l_Lean_Compiler_LCNF_mkFreshBinderName(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_2);
x_12 = lean_is_marked_borrowed(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_10);
x_16 = l_Lean_Compiler_LCNF_mkParam(x_10, x_14, x_12, x_4, x_5, x_6, x_7, x_15);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
x_35 = lean_ctor_get(x_20, 2);
x_36 = lean_ctor_get(x_20, 3);
x_37 = lean_ctor_get(x_20, 4);
x_38 = lean_ctor_get(x_20, 5);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_39 = lean_ctor_get(x_17, 0);
lean_inc(x_39);
x_40 = 0;
x_41 = 0;
x_42 = l_Lean_LocalContext_mkLocalDecl(x_33, x_39, x_10, x_2, x_40, x_41);
x_43 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_34);
lean_ctor_set(x_43, 2, x_35);
lean_ctor_set(x_43, 3, x_36);
lean_ctor_set(x_43, 4, x_37);
lean_ctor_set(x_43, 5, x_38);
x_44 = lean_st_ref_set(x_3, x_43, x_21);
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
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_17);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_13);
if (x_48 == 0)
{
return x_13;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_13, 0);
x_50 = lean_ctor_get(x_13, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_13);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_inc(x_1);
x_12 = l_Lean_Compiler_LCNF_mkLetDecl(x_1, x_2, x_5, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_6, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 4);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = 0;
x_23 = 0;
x_24 = l_Lean_LocalContext_mkLetDecl(x_19, x_21, x_1, x_3, x_4, x_22, x_23);
lean_inc(x_13);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_13);
x_26 = lean_array_push(x_20, x_25);
lean_ctor_set(x_16, 4, x_26);
lean_ctor_set(x_16, 0, x_24);
x_27 = lean_st_ref_set(x_6, x_16, x_17);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_13);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_13);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
x_34 = lean_ctor_get(x_16, 2);
x_35 = lean_ctor_get(x_16, 3);
x_36 = lean_ctor_get(x_16, 4);
x_37 = lean_ctor_get(x_16, 5);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_38 = lean_ctor_get(x_13, 0);
lean_inc(x_38);
x_39 = 0;
x_40 = 0;
x_41 = l_Lean_LocalContext_mkLetDecl(x_32, x_38, x_1, x_3, x_4, x_39, x_40);
lean_inc(x_13);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_13);
x_43 = lean_array_push(x_36, x_42);
x_44 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_33);
lean_ctor_set(x_44, 2, x_34);
lean_ctor_set(x_44, 3, x_35);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set(x_44, 5, x_37);
x_45 = lean_st_ref_set(x_6, x_44, x_17);
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
lean_ctor_set(x_48, 0, x_13);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___lambda__1(x_13, x_4, x_2, x_3, x_17, x_6, x_7, x_8, x_9, x_10, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_box(1);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___lambda__1(x_19, x_4, x_2, x_3, x_21, x_6, x_7, x_8, x_9, x_10, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
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
x_9 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
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
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_noConfusionExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_projectionFnInfoExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Eq", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ndrec", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__3;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_1);
x_5 = lean_environment_find(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_inc(x_4);
lean_inc(x_1);
x_6 = l_Lean_isCasesOnRecursor(x_1, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1;
lean_inc(x_4);
lean_inc(x_1);
x_8 = l_Lean_TagDeclarationExtension_isTagged(x_7, x_1, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_instInhabitedProjectionFunctionInfo;
x_10 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2;
lean_inc(x_4);
x_11 = l_Lean_MapDeclarationExtension_contains___rarg(x_9, x_10, x_1, x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__5;
x_13 = lean_name_eq(x_4, x_12);
lean_dec(x_4);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_4);
x_14 = 1;
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_1);
x_15 = 1;
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_4);
lean_dec(x_1);
x_16 = 1;
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
lean_dec(x_5);
switch (lean_obj_tag(x_17)) {
case 4:
{
uint8_t x_18; 
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_1);
x_18 = 1;
return x_18;
}
case 6:
{
uint8_t x_19; 
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_1);
x_19 = 1;
return x_19;
}
case 7:
{
uint8_t x_20; 
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_1);
x_20 = 1;
return x_20;
}
default: 
{
uint8_t x_21; 
lean_dec(x_17);
lean_inc(x_4);
lean_inc(x_1);
x_21 = l_Lean_isCasesOnRecursor(x_1, x_4);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1;
lean_inc(x_4);
lean_inc(x_1);
x_23 = l_Lean_TagDeclarationExtension_isTagged(x_22, x_1, x_4);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l_Lean_instInhabitedProjectionFunctionInfo;
x_25 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2;
lean_inc(x_4);
x_26 = l_Lean_MapDeclarationExtension_contains___rarg(x_24, x_25, x_1, x_4);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__5;
x_28 = lean_name_eq(x_4, x_27);
lean_dec(x_4);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_4);
x_29 = 1;
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_4);
lean_dec(x_1);
x_30 = 1;
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_4);
lean_dec(x_1);
x_31 = 1;
return x_31;
}
}
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_3);
lean_dec(x_1);
x_32 = 0;
return x_32;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
lean_inc(x_2);
x_9 = l_Lean_mkAppN(x_1, x_2);
x_10 = 0;
x_11 = 1;
x_12 = 1;
x_13 = l_Lean_Meta_mkLambdaFVars(x_2, x_9, x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_st_ref_get(x_3, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
x_17 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_9);
lean_ctor_set(x_18, 5, x_15);
x_19 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__17;
x_20 = lean_st_mk_ref(x_19, x_13);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_21);
lean_inc(x_18);
lean_inc(x_1);
x_23 = lean_infer_type(x_1, x_18, x_21, x_6, x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_2);
x_27 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___lambda__1___boxed), 8, 1);
lean_closure_set(x_27, 0, x_1);
lean_inc(x_21);
x_28 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__5___rarg(x_24, x_26, x_27, x_18, x_21, x_6, x_7, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_st_ref_get(x_21, x_30);
lean_dec(x_21);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_29);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_21);
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
else
{
uint8_t x_40; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
return x_23;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_23, 0);
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_23);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_8);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
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
lean_object* x_7; 
lean_dec(x_1);
lean_inc(x_4);
x_7 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit(x_4);
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; size_t x_14; uint8_t x_15; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Expr_lam___override(x_2, x_3, x_4, x_5);
x_14 = lean_ptr_addr(x_3);
x_15 = lean_usize_dec_eq(x_14, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_4);
x_16 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_18 = lean_ptr_addr(x_7);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_13);
x_20 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_5, x_5);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_13);
x_22 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_22;
}
else
{
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
}
}
else
{
uint8_t x_23; 
x_23 = lean_expr_has_loose_bvar(x_9, x_11);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_expr_lower_loose_bvars(x_9, x_24, x_24);
lean_dec(x_9);
return x_25;
}
else
{
lean_object* x_26; size_t x_27; uint8_t x_28; 
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_26 = l_Lean_Expr_lam___override(x_2, x_3, x_4, x_5);
x_27 = lean_ptr_addr(x_3);
x_28 = lean_usize_dec_eq(x_27, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_26);
lean_dec(x_4);
x_29 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_29;
}
else
{
size_t x_30; size_t x_31; uint8_t x_32; 
x_30 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_31 = lean_ptr_addr(x_7);
x_32 = lean_usize_dec_eq(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_26);
x_33 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_5, x_5);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_26);
x_35 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_35;
}
else
{
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_26;
}
}
}
}
}
}
else
{
lean_object* x_36; size_t x_37; uint8_t x_38; 
lean_dec(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_36 = l_Lean_Expr_lam___override(x_2, x_3, x_4, x_5);
x_37 = lean_ptr_addr(x_3);
x_38 = lean_usize_dec_eq(x_37, x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_36);
lean_dec(x_4);
x_39 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_39;
}
else
{
size_t x_40; size_t x_41; uint8_t x_42; 
x_40 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_41 = lean_ptr_addr(x_7);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_36);
x_43 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_43;
}
else
{
uint8_t x_44; 
x_44 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_5, x_5);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_36);
x_45 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_45;
}
else
{
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_36;
}
}
}
}
}
else
{
lean_object* x_46; size_t x_47; uint8_t x_48; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_46 = l_Lean_Expr_lam___override(x_2, x_3, x_4, x_5);
x_47 = lean_ptr_addr(x_3);
x_48 = lean_usize_dec_eq(x_47, x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_46);
lean_dec(x_4);
x_49 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_49;
}
else
{
size_t x_50; size_t x_51; uint8_t x_52; 
x_50 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_51 = lean_ptr_addr(x_7);
x_52 = lean_usize_dec_eq(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_46);
x_53 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_53;
}
else
{
uint8_t x_54; 
x_54 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_5, x_5);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_46);
x_55 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_55;
}
else
{
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_46;
}
}
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
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_litToValue___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_ToLCNF_litToValue(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_litToValue(x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
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
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_2, x_11);
lean_dec(x_2);
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(x_13);
x_16 = lean_expr_instantiate1(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_1 = x_16;
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_nat_add(x_12, x_11);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_18);
x_19 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_1 = x_20;
x_2 = x_18;
x_8 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_8);
return x_27;
}
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__3(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Expr_hash(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_expr_eqv(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_expr_eqv(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_expr_eqv(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__2;
x_52 = lean_usize_land(x_2, x_51);
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(0);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_expr_eqv(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__4(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__3;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__3(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__4(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__3;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__3(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Expr_hash(x_2);
x_8 = lean_uint64_to_usize(x_7);
x_9 = 1;
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2(x_5, x_8, x_9, x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_Expr_hash(x_2);
x_16 = lean_uint64_to_usize(x_15);
x_17 = 1;
x_18 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2(x_13, x_16, x_17, x_2, x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_14, x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_instMonadCompilerM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__1;
x_2 = l_Lean_Compiler_LCNF_instInhabitedArg;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__2;
x_9 = lean_panic_fn(x_8, x_1);
x_10 = lean_apply_6(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_expr_eqv(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__7(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_expr_eqv(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__8(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Expr_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__7(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9___closed__2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_2);
x_14 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__1(x_13, x_1, x_2);
lean_ctor_set(x_10, 1, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
x_22 = lean_ctor_get(x_10, 2);
x_23 = lean_ctor_get(x_10, 3);
x_24 = lean_ctor_get(x_10, 4);
x_25 = lean_ctor_get(x_10, 5);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
lean_inc(x_2);
x_26 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__1(x_21, x_1, x_2);
x_27 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set(x_27, 5, x_25);
x_28 = lean_st_ref_set(x_3, x_27, x_11);
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
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.ToLCNF", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitCore", 42);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__2;
x_3 = lean_unsigned_to_nat(431u);
x_4 = lean_unsigned_to_nat(57u);
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_dec(x_2);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_st_ref_get(x_3, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 5);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_13, x_9);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_9);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_9);
x_17 = lean_box(0);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
}
case 4:
{
lean_object* x_19; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_19 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
case 5:
{
lean_object* x_27; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_28, x_3, x_4, x_5, x_6, x_7, x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
case 6:
{
lean_object* x_35; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_35 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_36, x_3, x_4, x_5, x_6, x_7, x_37);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_38;
}
else
{
uint8_t x_39; 
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
case 8:
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_44 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(x_1, x_43, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_45, x_3, x_4, x_5, x_6, x_7, x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
case 9:
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_53 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(x_52, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_54, x_3, x_4, x_5, x_6, x_7, x_55);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 0);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_53);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
case 10:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_63 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData(x_61, x_62, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_64, x_3, x_4, x_5, x_6, x_7, x_65);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_66;
}
else
{
uint8_t x_67; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
return x_63;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_63, 0);
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_63);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
case 11:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_1, 2);
lean_inc(x_73);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_74 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(x_71, x_72, x_73, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_75, x_3, x_4, x_5, x_6, x_7, x_76);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_77;
}
else
{
uint8_t x_78; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_74);
if (x_78 == 0)
{
return x_74;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_74, 0);
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_74);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
default: 
{
lean_object* x_82; lean_object* x_83; 
x_82 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__4;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_83 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_82, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_84, x_3, x_4, x_5, x_6, x_7, x_85);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_86;
}
else
{
uint8_t x_87; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
return x_83;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_83, 0);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_83);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 7);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 8);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 9);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 10);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
x_20 = lean_nat_dec_eq(x_11, x_12);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_22 = lean_ctor_get(x_5, 10);
lean_dec(x_22);
x_23 = lean_ctor_get(x_5, 9);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 8);
lean_dec(x_24);
x_25 = lean_ctor_get(x_5, 7);
lean_dec(x_25);
x_26 = lean_ctor_get(x_5, 6);
lean_dec(x_26);
x_27 = lean_ctor_get(x_5, 5);
lean_dec(x_27);
x_28 = lean_ctor_get(x_5, 4);
lean_dec(x_28);
x_29 = lean_ctor_get(x_5, 3);
lean_dec(x_29);
x_30 = lean_ctor_get(x_5, 2);
lean_dec(x_30);
x_31 = lean_ctor_get(x_5, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_5, 0);
lean_dec(x_32);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_11, x_33);
lean_dec(x_11);
lean_ctor_set(x_5, 3, x_34);
x_35 = lean_st_ref_get(x_2, x_7);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_1);
x_40 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6(x_39, x_1);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_free_object(x_35);
x_41 = lean_box(0);
x_42 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2(x_1, x_41, x_2, x_3, x_4, x_5, x_6, x_38);
return x_42;
}
else
{
lean_object* x_43; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
lean_ctor_set(x_35, 0, x_43);
return x_35;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_35, 0);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_35);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_1);
x_47 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6(x_46, x_1);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_box(0);
x_49 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2(x_1, x_48, x_2, x_3, x_4, x_5, x_6, x_45);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_5);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_11, x_52);
lean_dec(x_11);
x_54 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_54, 0, x_8);
lean_ctor_set(x_54, 1, x_9);
lean_ctor_set(x_54, 2, x_10);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set(x_54, 4, x_12);
lean_ctor_set(x_54, 5, x_13);
lean_ctor_set(x_54, 6, x_14);
lean_ctor_set(x_54, 7, x_15);
lean_ctor_set(x_54, 8, x_16);
lean_ctor_set(x_54, 9, x_17);
lean_ctor_set(x_54, 10, x_18);
lean_ctor_set_uint8(x_54, sizeof(void*)*11, x_19);
x_55 = lean_st_ref_get(x_2, x_7);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
lean_inc(x_1);
x_60 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6(x_59, x_1);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_58);
x_61 = lean_box(0);
x_62 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2(x_1, x_61, x_2, x_3, x_4, x_54, x_6, x_57);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_54);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec(x_60);
if (lean_is_scalar(x_58)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_58;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_57);
return x_64;
}
}
}
else
{
lean_object* x_65; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_65 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9(x_13, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_65;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_expr_instantiate_rev(x_10, x_2);
lean_dec(x_10);
x_14 = lean_expr_instantiate_rev(x_11, x_2);
lean_dec(x_11);
x_41 = lean_st_ref_get(x_3, x_8);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_box(0);
x_46 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
x_47 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_44);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set(x_49, 3, x_45);
lean_ctor_set(x_49, 4, x_48);
lean_ctor_set(x_49, 5, x_45);
x_50 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__17;
x_51 = lean_st_mk_ref(x_50, x_43);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_52);
lean_inc(x_13);
x_54 = l_Lean_Meta_isProp(x_13, x_49, x_52, x_6, x_7, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_st_ref_get(x_52, x_56);
lean_dec(x_52);
x_58 = lean_unbox(x_55);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_55);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
x_60 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(x_13, x_3, x_4, x_5, x_6, x_7, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_unbox(x_61);
lean_dec(x_61);
x_15 = x_63;
x_16 = x_62;
goto block_40;
}
else
{
uint8_t x_64; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_57, 1);
lean_inc(x_68);
lean_dec(x_57);
x_69 = lean_unbox(x_55);
lean_dec(x_55);
x_15 = x_69;
x_16 = x_68;
goto block_40;
}
}
else
{
uint8_t x_70; 
lean_dec(x_52);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_54);
if (x_70 == 0)
{
return x_54;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_54, 0);
x_72 = lean_ctor_get(x_54, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_54);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
block_40:
{
if (x_15 == 0)
{
lean_object* x_17; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_13, x_3, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_14);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_14, x_3, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(x_9, x_13, x_14, x_18, x_21, x_3, x_4, x_5, x_6, x_7, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Expr_fvar___override(x_26);
x_28 = lean_array_push(x_2, x_27);
x_1 = x_12;
x_2 = x_28;
x_8 = x_25;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
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
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_17);
if (x_34 == 0)
{
return x_17;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_17, 0);
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_17);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; 
lean_dec(x_13);
lean_dec(x_9);
x_38 = lean_array_push(x_2, x_14);
x_1 = x_12;
x_2 = x_38;
x_8 = x_16;
goto _start;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_75 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_74, x_3, x_4, x_5, x_6, x_7, x_8);
return x_75;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_dec(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(x_2, x_4, x_5, x_6, x_7, x_8, x_13);
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
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
x_15 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_16);
lean_ctor_set(x_17, 5, x_13);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__17;
x_19 = lean_st_mk_ref(x_18, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_20);
lean_inc(x_1);
x_22 = lean_infer_type(x_1, x_17, x_20, x_6, x_7, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_20, x_24);
lean_dec(x_20);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_get(x_3, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_15);
lean_ctor_set(x_31, 3, x_13);
lean_ctor_set(x_31, 4, x_16);
lean_ctor_set(x_31, 5, x_13);
x_32 = lean_st_mk_ref(x_18, x_29);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
lean_inc(x_23);
x_35 = l_Lean_Meta_isProp(x_23, x_31, x_33, x_6, x_7, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_st_ref_get(x_33, x_37);
lean_dec(x_33);
x_39 = lean_unbox(x_36);
lean_dec(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_box(0);
x_42 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2(x_23, x_1, x_41, x_3, x_4, x_5, x_6, x_7, x_40);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_38, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_38, 0, x_45);
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_dec(x_38);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_33);
lean_dec(x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_35);
if (x_49 == 0)
{
return x_35;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get(x_35, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_35);
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
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_22);
if (x_53 == 0)
{
return x_22;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_22, 0);
x_55 = lean_ctor_get(x_22, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_22);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof(x_1);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 7);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 8);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 9);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 10);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
x_21 = lean_nat_dec_eq(x_12, x_13);
if (x_8 == 0)
{
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_23 = lean_ctor_get(x_5, 10);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 9);
lean_dec(x_24);
x_25 = lean_ctor_get(x_5, 8);
lean_dec(x_25);
x_26 = lean_ctor_get(x_5, 7);
lean_dec(x_26);
x_27 = lean_ctor_get(x_5, 6);
lean_dec(x_27);
x_28 = lean_ctor_get(x_5, 5);
lean_dec(x_28);
x_29 = lean_ctor_get(x_5, 4);
lean_dec(x_29);
x_30 = lean_ctor_get(x_5, 3);
lean_dec(x_30);
x_31 = lean_ctor_get(x_5, 2);
lean_dec(x_31);
x_32 = lean_ctor_get(x_5, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_5, 0);
lean_dec(x_33);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_12, x_34);
lean_dec(x_12);
lean_ctor_set(x_5, 3, x_35);
x_36 = lean_box(0);
x_37 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__3(x_1, x_36, x_2, x_3, x_4, x_5, x_6, x_7);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_5);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_12, x_38);
lean_dec(x_12);
x_40 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_40, 0, x_9);
lean_ctor_set(x_40, 1, x_10);
lean_ctor_set(x_40, 2, x_11);
lean_ctor_set(x_40, 3, x_39);
lean_ctor_set(x_40, 4, x_13);
lean_ctor_set(x_40, 5, x_14);
lean_ctor_set(x_40, 6, x_15);
lean_ctor_set(x_40, 7, x_16);
lean_ctor_set(x_40, 8, x_17);
lean_ctor_set(x_40, 9, x_18);
lean_ctor_set(x_40, 10, x_19);
lean_ctor_set_uint8(x_40, sizeof(void*)*11, x_20);
x_41 = lean_box(0);
x_42 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__3(x_1, x_41, x_2, x_3, x_4, x_40, x_6, x_7);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_43 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9(x_14, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_43;
}
}
else
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
if (x_21 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_7);
return x_45;
}
else
{
lean_object* x_46; 
x_46 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9(x_14, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_7(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_11);
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
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_f", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toCode(x_11, x_2, x_3, x_4, x_5, x_6, x_12);
lean_dec(x_2);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__2;
x_17 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_8, x_14, x_16, x_3, x_4, x_5, x_6, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_35; 
lean_inc(x_1);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit(x_1);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_35 = l_Lean_Expr_isLambda(x_8);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand(x_12, x_8);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_1);
x_37 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_8, x_2, x_3, x_4, x_5, x_6, x_11);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_8);
x_38 = lean_box(0);
x_13 = x_38;
goto block_34;
}
}
else
{
lean_object* x_39; 
lean_dec(x_12);
lean_dec(x_8);
x_39 = lean_box(0);
x_13 = x_39;
goto block_34;
}
block_34:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_visitLambda___boxed), 7, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___closed__1;
x_16 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___rarg(x_16, x_2, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = l_Lean_Compiler_LCNF_ToLCNF_pushElement(x_20, x_2, x_3, x_4, x_5, x_6, x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_2);
x_9 = l_Lean_Expr_mdata___override(x_1, x_2);
x_10 = l_Lean_letFunAnnotation_x3f(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 5)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 6)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 2);
lean_inc(x_17);
lean_dec(x_13);
x_18 = 1;
x_19 = l_Lean_Expr_letE___override(x_15, x_16, x_14, x_17, x_18);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_21 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_12);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_12);
x_23 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_23;
}
}
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
if (lean_obj_tag(x_11) == 1)
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
x_15 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
x_16 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_4);
return x_16;
}
else
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
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_12, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_14, x_2, x_16);
x_2 = x_19;
x_3 = x_20;
x_9 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get_size(x_2);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__1(x_21, x_22, x_2, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
x_28 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_26, x_27, x_4, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_4);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_16, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_16, 0, x_35);
return x_16;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_dec(x_16);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_instInhabitedProjectionFunctionInfo;
x_13 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2;
x_14 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_12, x_13, x_11, x_1);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_instInhabitedProjectionFunctionInfo;
x_19 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2;
x_20 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_18, x_19, x_17, x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Quot", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lift", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mk", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("casesOn", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__3;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rec", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__3;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("And", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Iff", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("False", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Empty", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__19;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__19;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4;
x_11 = lean_name_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6;
x_13 = lean_name_eq(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8;
x_15 = lean_name_eq(x_9, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10;
x_17 = lean_name_eq(x_9, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__5;
x_19 = lean_name_eq(x_9, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12;
x_21 = lean_name_eq(x_9, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__14;
x_23 = lean_name_eq(x_9, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15;
x_25 = lean_name_eq(x_9, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__16;
x_27 = lean_name_eq(x_9, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__18;
x_29 = lean_name_eq(x_9, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__20;
x_31 = lean_name_eq(x_9, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__21;
x_33 = lean_name_eq(x_9, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22;
x_35 = lean_name_eq(x_9, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_9);
x_36 = l_Lean_Compiler_LCNF_getCasesInfo_x3f(x_9, x_5, x_6, x_7);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_9);
x_39 = l_Lean_Compiler_LCNF_getCtorArity_x3f(x_9, x_5, x_6, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_st_ref_get(x_6, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1;
lean_inc(x_9);
x_47 = l_Lean_TagDeclarationExtension_isTagged(x_46, x_45, x_9);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__3(x_9, x_2, x_3, x_4, x_5, x_6, x_44);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_51);
x_53 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_52);
x_54 = lean_mk_array(x_52, x_53);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_sub(x_52, x_55);
lean_dec(x_52);
x_57 = l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__4(x_1, x_54, x_56, x_2, x_3, x_4, x_5, x_6, x_50);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_dec(x_48);
x_59 = lean_ctor_get(x_49, 0);
lean_inc(x_59);
lean_dec(x_49);
x_60 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(x_59, x_1, x_2, x_3, x_4, x_5, x_6, x_58);
return x_60;
}
}
else
{
lean_object* x_61; 
lean_dec(x_9);
x_61 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion(x_1, x_2, x_3, x_4, x_5, x_6, x_44);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_9);
x_62 = lean_ctor_get(x_39, 1);
lean_inc(x_62);
lean_dec(x_39);
x_63 = lean_ctor_get(x_40, 0);
lean_inc(x_63);
lean_dec(x_40);
x_64 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(x_63, x_1, x_2, x_3, x_4, x_5, x_6, x_62);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_9);
x_69 = lean_ctor_get(x_36, 1);
lean_inc(x_69);
lean_dec(x_36);
x_70 = lean_ctor_get(x_37, 0);
lean_inc(x_70);
lean_dec(x_37);
x_71 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(x_70, x_1, x_2, x_3, x_4, x_5, x_6, x_69);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_36);
if (x_72 == 0)
{
return x_36;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_36, 0);
x_74 = lean_ctor_get(x_36, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_36);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; 
lean_dec(x_9);
x_76 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_76;
}
}
else
{
lean_object* x_77; 
lean_dec(x_9);
x_77 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_77;
}
}
else
{
lean_object* x_78; 
lean_dec(x_9);
x_78 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_9);
x_79 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_9);
x_80 = lean_unsigned_to_nat(4u);
x_81 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(x_1, x_80, x_2, x_3, x_4, x_5, x_6, x_7);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_9);
x_82 = lean_unsigned_to_nat(4u);
x_83 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(x_1, x_82, x_2, x_3, x_4, x_5, x_6, x_7);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_9);
x_84 = lean_unsigned_to_nat(3u);
x_85 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(x_1, x_84, x_2, x_3, x_4, x_5, x_6, x_7);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_9);
x_86 = lean_unsigned_to_nat(3u);
x_87 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(x_1, x_86, x_2, x_3, x_4, x_5, x_6, x_7);
return x_87;
}
}
else
{
lean_object* x_88; 
lean_dec(x_9);
x_88 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_88;
}
}
else
{
lean_object* x_89; 
lean_dec(x_9);
x_89 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_89;
}
}
else
{
lean_object* x_90; 
lean_dec(x_9);
x_90 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_9);
x_91 = lean_unsigned_to_nat(3u);
x_92 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(x_91, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_92;
}
}
else
{
lean_object* x_93; 
lean_dec(x_9);
x_93 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_8);
x_94 = lean_unsigned_to_nat(0u);
x_95 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_94);
x_96 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_95);
x_97 = lean_mk_array(x_95, x_96);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_sub(x_95, x_98);
lean_dec(x_95);
x_100 = l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2(x_1, x_97, x_99, x_2, x_3, x_4, x_5, x_6, x_7);
return x_100;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_dec(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(x_2, x_4, x_5, x_6, x_7, x_8, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_1, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l_Lean_Compiler_LCNF_isPredicateType(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_free_object(x_16);
x_21 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_2, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_33 = lean_box(0);
lean_ctor_set(x_16, 0, x_33);
return x_16;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
x_36 = l_Lean_Compiler_LCNF_isPredicateType(x_34);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_2, x_4, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
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
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_38);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_35);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_16);
if (x_49 == 0)
{
return x_16;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_16, 0);
x_51 = lean_ctor_get(x_16, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_16);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_10);
if (x_53 == 0)
{
return x_10;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_10, 0);
x_55 = lean_ctor_get(x_10, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_10);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
x_15 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_16);
lean_ctor_set(x_17, 5, x_13);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__17;
x_19 = lean_st_mk_ref(x_18, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_20);
lean_inc(x_1);
x_22 = lean_infer_type(x_1, x_17, x_20, x_6, x_7, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_20, x_24);
lean_dec(x_20);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_get(x_3, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_15);
lean_ctor_set(x_31, 3, x_13);
lean_ctor_set(x_31, 4, x_16);
lean_ctor_set(x_31, 5, x_13);
x_32 = lean_st_mk_ref(x_18, x_29);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
lean_inc(x_23);
x_35 = l_Lean_Meta_isProp(x_23, x_31, x_33, x_6, x_7, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_st_ref_get(x_33, x_37);
lean_dec(x_33);
x_39 = lean_unbox(x_36);
lean_dec(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_box(0);
x_42 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg___lambda__1(x_23, x_1, x_41, x_3, x_4, x_5, x_6, x_7, x_40);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_38, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_38, 0, x_45);
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_dec(x_38);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_33);
lean_dec(x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_35);
if (x_49 == 0)
{
return x_35;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get(x_35, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_35);
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
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_22);
if (x_53 == 0)
{
return x_22;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_22, 0);
x_55 = lean_ctor_get(x_22, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_22);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg___lambda__2(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitAppDefaultConst", 53);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1;
x_3 = lean_unsigned_to_nat(473u);
x_4 = lean_unsigned_to_nat(34u);
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_array_get_size(x_2);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__1(x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_15);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
x_19 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_17, x_18, x_3, x_4, x_5, x_6, x_7, x_16);
lean_dec(x_3);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__2;
x_25 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_24, x_3, x_4, x_5, x_6, x_7, x_8);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_4, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_16);
x_18 = lean_ctor_get(x_5, 2);
x_19 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__6;
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
lean_inc(x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_25);
x_27 = lean_ctor_get(x_5, 2);
x_28 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__6;
lean_inc(x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
x_30 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_1);
lean_inc(x_8);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown constant '", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = lean_environment_find(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_8);
x_14 = lean_box(0);
x_15 = l_Lean_Expr_const___override(x_1, x_14);
x_16 = l_Lean_MessageData_ofExpr(x_15);
x_17 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__2;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__4;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__2(x_20, x_2, x_3, x_4, x_5, x_6, x_11);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
lean_ctor_set(x_8, 0, x_22);
return x_8;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_1);
x_26 = lean_environment_find(x_25, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_box(0);
x_28 = l_Lean_Expr_const___override(x_1, x_27);
x_29 = l_Lean_MessageData_ofExpr(x_28);
x_30 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__2;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__4;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__2(x_33, x_2, x_3, x_4, x_5, x_6, x_24);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_1);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec(x_26);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
return x_36;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitProjFn", 44);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1;
x_3 = lean_unsigned_to_nat(655u);
x_4 = lean_unsigned_to_nat(45u);
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = l_Lean_Name_getPrefix(x_9);
lean_dec(x_9);
x_11 = l_Lean_Compiler_LCNF_builtinRuntimeTypes;
x_12 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1(x_14, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Core_instantiateValueLevelParams(x_17, x_15, x_6, x_7, x_18);
lean_dec(x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_22);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_23);
x_25 = lean_mk_array(x_23, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_23, x_26);
lean_dec(x_23);
x_28 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_25, x_27);
x_29 = l_Lean_Expr_beta(x_20, x_28);
x_30 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_29, x_3, x_4, x_5, x_6, x_7, x_21);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
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
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
return x_16;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_16);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_13);
lean_dec(x_2);
x_39 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__2;
x_40 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_39, x_3, x_4, x_5, x_6, x_7, x_8);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_unsigned_to_nat(0u);
x_42 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_41);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
lean_dec(x_1);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_43, x_44);
lean_dec(x_43);
x_46 = lean_nat_dec_lt(x_42, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
x_47 = l_Lean_Expr_getAppFn(x_2);
x_48 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_42);
x_49 = lean_mk_array(x_42, x_48);
x_50 = lean_nat_sub(x_42, x_44);
lean_dec(x_42);
x_51 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_49, x_50);
x_52 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(x_47, x_51, x_3, x_4, x_5, x_6, x_7, x_8);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_nat_sub(x_45, x_42);
lean_dec(x_42);
lean_dec(x_45);
lean_inc(x_7);
lean_inc(x_6);
x_54 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(x_2, x_53, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_55, x_3, x_4, x_5, x_6, x_7, x_56);
return x_57;
}
else
{
uint8_t x_58; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_4, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_16);
x_18 = lean_ctor_get(x_5, 2);
x_19 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__6;
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
lean_inc(x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_25);
x_27 = lean_ctor_get(x_5, 2);
x_28 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__6;
lean_inc(x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
x_30 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_1);
lean_inc(x_8);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_get_size(x_1);
x_11 = l_Array_toSubarray___rarg(x_1, x_2, x_10);
x_12 = l_Array_ofSubarray___rarg(x_11);
x_13 = l_Lean_mkAppN(x_3, x_12);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_13, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("code generator failed, unsupported occurrence of `", 50);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("`", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_add(x_1, x_14);
lean_dec(x_1);
x_16 = lean_nat_dec_lt(x_15, x_2);
x_17 = lean_st_ref_get(x_8, x_13);
if (x_16 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_15);
x_111 = lean_ctor_get(x_17, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_17, 1);
lean_inc(x_112);
lean_dec(x_17);
x_113 = l_Lean_instInhabitedExpr;
x_114 = l___private_Init_Util_0__outOfBounds___rarg(x_113);
x_18 = x_114;
x_19 = x_111;
x_20 = x_112;
goto block_110;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_17, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_17, 1);
lean_inc(x_116);
lean_dec(x_17);
x_117 = lean_array_fget(x_6, x_15);
lean_dec(x_15);
x_18 = x_117;
x_19 = x_115;
x_20 = x_116;
goto block_110;
}
block_110:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
x_24 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set(x_26, 4, x_25);
lean_ctor_set(x_26, 5, x_22);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__17;
x_28 = lean_st_mk_ref(x_27, x_20);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_29);
x_31 = lean_whnf(x_18, x_26, x_29, x_11, x_12, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_29, x_33);
lean_dec(x_29);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Expr_toCtorIfLit(x_7);
x_37 = l_Lean_Expr_toCtorIfLit(x_32);
x_38 = lean_st_ref_get(x_12, x_35);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_st_ref_get(x_12, x_40);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Expr_isConstructorApp_x3f(x_41, x_36);
lean_dec(x_36);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
lean_dec(x_37);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_47 = l_Lean_MessageData_ofName(x_3);
x_48 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__2;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__4;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___spec__1(x_51, x_8, x_9, x_10, x_11, x_12, x_44);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
lean_dec(x_46);
x_54 = l_Lean_Expr_isConstructorApp_x3f(x_45, x_37);
lean_dec(x_37);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_53);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_55 = l_Lean_MessageData_ofName(x_3);
x_56 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__2;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__4;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___spec__1(x_59, x_8, x_9, x_10, x_11, x_12, x_44);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_3);
x_61 = lean_ctor_get(x_54, 0);
lean_inc(x_61);
lean_dec(x_54);
x_62 = lean_ctor_get(x_53, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_name_eq(x_63, x_65);
lean_dec(x_65);
lean_dec(x_63);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_53);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_67 = lean_st_ref_get(x_8, x_44);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_71, 0, x_23);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_24);
lean_ctor_set(x_71, 3, x_22);
lean_ctor_set(x_71, 4, x_25);
lean_ctor_set(x_71, 5, x_22);
x_72 = lean_st_mk_ref(x_27, x_69);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_73);
x_75 = lean_infer_type(x_4, x_71, x_73, x_11, x_12, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_st_ref_get(x_73, x_77);
lean_dec(x_73);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
lean_inc(x_12);
lean_inc(x_11);
x_80 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_76, x_8, x_9, x_10, x_11, x_12, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_81, x_8, x_9, x_10, x_11, x_12, x_82);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_83;
}
else
{
uint8_t x_84; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_84 = !lean_is_exclusive(x_80);
if (x_84 == 0)
{
return x_80;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_80, 0);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_80);
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
lean_dec(x_73);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_88 = !lean_is_exclusive(x_75);
if (x_88 == 0)
{
return x_75;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_75, 0);
x_90 = lean_ctor_get(x_75, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_75);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_add(x_5, x_92);
x_94 = lean_nat_dec_lt(x_5, x_2);
lean_dec(x_2);
x_95 = lean_ctor_get(x_53, 4);
lean_inc(x_95);
lean_dec(x_53);
lean_inc(x_93);
lean_inc(x_6);
x_96 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__1), 9, 2);
lean_closure_set(x_96, 0, x_6);
lean_closure_set(x_96, 1, x_93);
if (x_94 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_6);
lean_dec(x_5);
x_97 = l_Lean_instInhabitedExpr;
x_98 = l___private_Init_Util_0__outOfBounds___rarg(x_97);
x_99 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___boxed), 8, 2);
lean_closure_set(x_99, 0, x_98);
lean_closure_set(x_99, 1, x_95);
x_100 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_100, 0, x_99);
lean_closure_set(x_100, 1, x_96);
x_101 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_4, x_93, x_100, x_8, x_9, x_10, x_11, x_12, x_44);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_array_fget(x_6, x_5);
lean_dec(x_5);
lean_dec(x_6);
x_103 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___boxed), 8, 2);
lean_closure_set(x_103, 0, x_102);
lean_closure_set(x_103, 1, x_95);
x_104 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_104, 0, x_103);
lean_closure_set(x_104, 1, x_96);
x_105 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_4, x_93, x_104, x_8, x_9, x_10, x_11, x_12, x_44);
return x_105;
}
}
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_29);
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
x_106 = !lean_is_exclusive(x_31);
if (x_106 == 0)
{
return x_31;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_31, 0);
x_108 = lean_ctor_get(x_31, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_31);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitNoConfusion", 49);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1;
x_3 = lean_unsigned_to_nat(611u);
x_4 = lean_unsigned_to_nat(42u);
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1;
x_3 = lean_unsigned_to_nat(613u);
x_4 = lean_unsigned_to_nat(56u);
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
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
x_10 = l_Lean_Name_getPrefix(x_9);
x_11 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_nat_add(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_17, x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_nat_add(x_19, x_20);
x_22 = lean_nat_add(x_21, x_18);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_23);
x_25 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_24);
x_26 = lean_mk_array(x_24, x_25);
x_27 = lean_nat_sub(x_24, x_18);
lean_dec(x_24);
lean_inc(x_1);
x_28 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_26, x_27);
x_29 = lean_array_get_size(x_28);
x_30 = lean_nat_dec_lt(x_19, x_29);
lean_inc(x_28);
lean_inc(x_22);
lean_inc(x_1);
x_31 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2), 13, 6);
lean_closure_set(x_31, 0, x_17);
lean_closure_set(x_31, 1, x_29);
lean_closure_set(x_31, 2, x_9);
lean_closure_set(x_31, 3, x_1);
lean_closure_set(x_31, 4, x_22);
lean_closure_set(x_31, 5, x_28);
if (x_30 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_28);
lean_dec(x_19);
x_32 = l_Lean_instInhabitedExpr;
x_33 = l___private_Init_Util_0__outOfBounds___rarg(x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_whnf___boxed), 6, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___boxed), 7, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_36, 0, x_35);
lean_closure_set(x_36, 1, x_31);
x_37 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_22, x_36, x_2, x_3, x_4, x_5, x_6, x_13);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_array_fget(x_28, x_19);
lean_dec(x_19);
lean_dec(x_28);
x_39 = lean_alloc_closure((void*)(l_Lean_Meta_whnf___boxed), 6, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___boxed), 7, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_41, 0, x_40);
lean_closure_set(x_41, 1, x_31);
x_42 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_22, x_41, x_2, x_3, x_4, x_5, x_6, x_13);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_1);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_dec(x_11);
x_44 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__3;
x_45 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_44, x_2, x_3, x_4, x_5, x_6, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_1);
x_50 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__2;
x_51 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_50, x_2, x_3, x_4, x_5, x_6, x_7);
return x_51;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_10);
x_12 = lean_nat_dec_lt(x_11, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_apply_6(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_14 = lean_nat_sub(x_2, x_11);
lean_dec(x_11);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(x_1, x_14, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_16, x_4, x_5, x_6, x_7, x_8, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_3, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_3, x_17);
lean_dec(x_3);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_7, 1);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_13);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_22);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_19, 1, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_13);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_7, 0);
lean_inc(x_31);
lean_dec(x_7);
x_32 = lean_ctor_get(x_22, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_34 = x_22;
} else {
 lean_dec_ref(x_22);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_19, 1, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_19);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_13);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_7);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_19, 1);
x_40 = lean_ctor_get(x_7, 0);
x_41 = lean_ctor_get(x_7, 1);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
x_45 = lean_ctor_get(x_21, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_dec(x_21);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_40, 2);
lean_inc(x_49);
x_50 = lean_nat_dec_lt(x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_ctor_set(x_19, 0, x_46);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_7);
lean_ctor_set(x_51, 1, x_13);
return x_51;
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_40);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_ctor_get(x_40, 2);
lean_dec(x_53);
x_54 = lean_ctor_get(x_40, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_40, 0);
lean_dec(x_55);
x_56 = lean_array_fget(x_47, x_48);
x_57 = lean_nat_add(x_48, x_17);
lean_dec(x_48);
lean_ctor_set(x_40, 1, x_57);
x_58 = lean_nat_dec_lt(x_4, x_2);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = l_Lean_instInhabitedExpr;
x_60 = l___private_Init_Util_0__outOfBounds___rarg(x_59);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_61 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_45, x_56, x_60, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = l_Lean_Compiler_LCNF_joinTypes(x_64, x_44);
x_67 = lean_array_push(x_43, x_65);
lean_ctor_set(x_39, 1, x_66);
lean_ctor_set(x_39, 0, x_67);
lean_ctor_set(x_19, 0, x_46);
x_68 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_68;
x_13 = x_63;
goto _start;
}
else
{
uint8_t x_70; 
lean_dec(x_40);
lean_dec(x_46);
lean_free_object(x_39);
lean_dec(x_44);
lean_dec(x_43);
lean_free_object(x_7);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_61);
if (x_70 == 0)
{
return x_61;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_61, 0);
x_72 = lean_ctor_get(x_61, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_61);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_array_fget(x_1, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_75 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_45, x_56, x_74, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l_Lean_Compiler_LCNF_joinTypes(x_78, x_44);
x_81 = lean_array_push(x_43, x_79);
lean_ctor_set(x_39, 1, x_80);
lean_ctor_set(x_39, 0, x_81);
lean_ctor_set(x_19, 0, x_46);
x_82 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_82;
x_13 = x_77;
goto _start;
}
else
{
uint8_t x_84; 
lean_dec(x_40);
lean_dec(x_46);
lean_free_object(x_39);
lean_dec(x_44);
lean_dec(x_43);
lean_free_object(x_7);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_84 = !lean_is_exclusive(x_75);
if (x_84 == 0)
{
return x_75;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_75, 0);
x_86 = lean_ctor_get(x_75, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_75);
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
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
lean_dec(x_40);
x_88 = lean_array_fget(x_47, x_48);
x_89 = lean_nat_add(x_48, x_17);
lean_dec(x_48);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_47);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_49);
x_91 = lean_nat_dec_lt(x_4, x_2);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = l_Lean_instInhabitedExpr;
x_93 = l___private_Init_Util_0__outOfBounds___rarg(x_92);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_94 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_45, x_88, x_93, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = l_Lean_Compiler_LCNF_joinTypes(x_97, x_44);
x_100 = lean_array_push(x_43, x_98);
lean_ctor_set(x_39, 1, x_99);
lean_ctor_set(x_39, 0, x_100);
lean_ctor_set(x_19, 0, x_46);
lean_ctor_set(x_7, 0, x_90);
x_101 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_101;
x_13 = x_96;
goto _start;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_90);
lean_dec(x_46);
lean_free_object(x_39);
lean_dec(x_44);
lean_dec(x_43);
lean_free_object(x_7);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_103 = lean_ctor_get(x_94, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_94, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_105 = x_94;
} else {
 lean_dec_ref(x_94);
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
x_107 = lean_array_fget(x_1, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_108 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_45, x_88, x_107, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
x_113 = l_Lean_Compiler_LCNF_joinTypes(x_111, x_44);
x_114 = lean_array_push(x_43, x_112);
lean_ctor_set(x_39, 1, x_113);
lean_ctor_set(x_39, 0, x_114);
lean_ctor_set(x_19, 0, x_46);
lean_ctor_set(x_7, 0, x_90);
x_115 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_115;
x_13 = x_110;
goto _start;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_90);
lean_dec(x_46);
lean_free_object(x_39);
lean_dec(x_44);
lean_dec(x_43);
lean_free_object(x_7);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_117 = lean_ctor_get(x_108, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_108, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_119 = x_108;
} else {
 lean_dec_ref(x_108);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_121 = lean_ctor_get(x_39, 0);
x_122 = lean_ctor_get(x_39, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_39);
x_123 = lean_ctor_get(x_21, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_21, 1);
lean_inc(x_124);
lean_dec(x_21);
x_125 = lean_ctor_get(x_40, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_40, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_40, 2);
lean_inc(x_127);
x_128 = lean_nat_dec_lt(x_126, x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_121);
lean_ctor_set(x_129, 1, x_122);
lean_ctor_set(x_19, 1, x_129);
lean_ctor_set(x_19, 0, x_124);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_7);
lean_ctor_set(x_130, 1, x_13);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 x_131 = x_40;
} else {
 lean_dec_ref(x_40);
 x_131 = lean_box(0);
}
x_132 = lean_array_fget(x_125, x_126);
x_133 = lean_nat_add(x_126, x_17);
lean_dec(x_126);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 3, 0);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_134, 2, x_127);
x_135 = lean_nat_dec_lt(x_4, x_2);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = l_Lean_instInhabitedExpr;
x_137 = l___private_Init_Util_0__outOfBounds___rarg(x_136);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_138 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_123, x_132, x_137, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
x_143 = l_Lean_Compiler_LCNF_joinTypes(x_141, x_122);
x_144 = lean_array_push(x_121, x_142);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
lean_ctor_set(x_19, 1, x_145);
lean_ctor_set(x_19, 0, x_124);
lean_ctor_set(x_7, 0, x_134);
x_146 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_146;
x_13 = x_140;
goto _start;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_134);
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_121);
lean_free_object(x_7);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_148 = lean_ctor_get(x_138, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_138, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_150 = x_138;
} else {
 lean_dec_ref(x_138);
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
x_152 = lean_array_fget(x_1, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_153 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_123, x_132, x_152, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec(x_154);
x_158 = l_Lean_Compiler_LCNF_joinTypes(x_156, x_122);
x_159 = lean_array_push(x_121, x_157);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
lean_ctor_set(x_19, 1, x_160);
lean_ctor_set(x_19, 0, x_124);
lean_ctor_set(x_7, 0, x_134);
x_161 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_161;
x_13 = x_155;
goto _start;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_134);
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_121);
lean_free_object(x_7);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_163 = lean_ctor_get(x_153, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_153, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_165 = x_153;
} else {
 lean_dec_ref(x_153);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_167 = lean_ctor_get(x_19, 1);
x_168 = lean_ctor_get(x_7, 0);
lean_inc(x_168);
lean_dec(x_7);
x_169 = lean_ctor_get(x_167, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_171 = x_167;
} else {
 lean_dec_ref(x_167);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_21, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_21, 1);
lean_inc(x_173);
lean_dec(x_21);
x_174 = lean_ctor_get(x_168, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_168, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_168, 2);
lean_inc(x_176);
x_177 = lean_nat_dec_lt(x_175, x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_172);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
if (lean_is_scalar(x_171)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_171;
}
lean_ctor_set(x_178, 0, x_169);
lean_ctor_set(x_178, 1, x_170);
lean_ctor_set(x_19, 1, x_178);
lean_ctor_set(x_19, 0, x_173);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_168);
lean_ctor_set(x_179, 1, x_19);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_13);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 x_181 = x_168;
} else {
 lean_dec_ref(x_168);
 x_181 = lean_box(0);
}
x_182 = lean_array_fget(x_174, x_175);
x_183 = lean_nat_add(x_175, x_17);
lean_dec(x_175);
if (lean_is_scalar(x_181)) {
 x_184 = lean_alloc_ctor(0, 3, 0);
} else {
 x_184 = x_181;
}
lean_ctor_set(x_184, 0, x_174);
lean_ctor_set(x_184, 1, x_183);
lean_ctor_set(x_184, 2, x_176);
x_185 = lean_nat_dec_lt(x_4, x_2);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = l_Lean_instInhabitedExpr;
x_187 = l___private_Init_Util_0__outOfBounds___rarg(x_186);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_188 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_172, x_182, x_187, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_ctor_get(x_189, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
lean_dec(x_189);
x_193 = l_Lean_Compiler_LCNF_joinTypes(x_191, x_170);
x_194 = lean_array_push(x_169, x_192);
if (lean_is_scalar(x_171)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_171;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
lean_ctor_set(x_19, 1, x_195);
lean_ctor_set(x_19, 0, x_173);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_184);
lean_ctor_set(x_196, 1, x_19);
x_197 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_197;
x_7 = x_196;
x_13 = x_190;
goto _start;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_184);
lean_dec(x_173);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_199 = lean_ctor_get(x_188, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_188, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_201 = x_188;
} else {
 lean_dec_ref(x_188);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_array_fget(x_1, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_204 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_172, x_182, x_203, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_ctor_get(x_205, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_208);
lean_dec(x_205);
x_209 = l_Lean_Compiler_LCNF_joinTypes(x_207, x_170);
x_210 = lean_array_push(x_169, x_208);
if (lean_is_scalar(x_171)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_171;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
lean_ctor_set(x_19, 1, x_211);
lean_ctor_set(x_19, 0, x_173);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_184);
lean_ctor_set(x_212, 1, x_19);
x_213 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_213;
x_7 = x_212;
x_13 = x_206;
goto _start;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_184);
lean_dec(x_173);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_215 = lean_ctor_get(x_204, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_204, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_217 = x_204;
} else {
 lean_dec_ref(x_204);
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
}
}
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_19, 1);
x_220 = lean_ctor_get(x_19, 0);
lean_inc(x_219);
lean_inc(x_220);
lean_dec(x_19);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_221 = lean_ctor_get(x_7, 0);
lean_inc(x_221);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_222 = x_7;
} else {
 lean_dec_ref(x_7);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_219, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_219, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_225 = x_219;
} else {
 lean_dec_ref(x_219);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_224);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_220);
lean_ctor_set(x_227, 1, x_226);
if (lean_is_scalar(x_222)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_222;
}
lean_ctor_set(x_228, 0, x_221);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_13);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_230 = lean_ctor_get(x_7, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_231 = x_7;
} else {
 lean_dec_ref(x_7);
 x_231 = lean_box(0);
}
x_232 = lean_ctor_get(x_219, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_219, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_234 = x_219;
} else {
 lean_dec_ref(x_219);
 x_234 = lean_box(0);
}
x_235 = lean_ctor_get(x_220, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_220, 1);
lean_inc(x_236);
lean_dec(x_220);
x_237 = lean_ctor_get(x_230, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_230, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_230, 2);
lean_inc(x_239);
x_240 = lean_nat_dec_lt(x_238, x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_235);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
if (lean_is_scalar(x_234)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_234;
}
lean_ctor_set(x_241, 0, x_232);
lean_ctor_set(x_241, 1, x_233);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_236);
lean_ctor_set(x_242, 1, x_241);
if (lean_is_scalar(x_231)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_231;
}
lean_ctor_set(x_243, 0, x_230);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_13);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 lean_ctor_release(x_230, 2);
 x_245 = x_230;
} else {
 lean_dec_ref(x_230);
 x_245 = lean_box(0);
}
x_246 = lean_array_fget(x_237, x_238);
x_247 = lean_nat_add(x_238, x_17);
lean_dec(x_238);
if (lean_is_scalar(x_245)) {
 x_248 = lean_alloc_ctor(0, 3, 0);
} else {
 x_248 = x_245;
}
lean_ctor_set(x_248, 0, x_237);
lean_ctor_set(x_248, 1, x_247);
lean_ctor_set(x_248, 2, x_239);
x_249 = lean_nat_dec_lt(x_4, x_2);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = l_Lean_instInhabitedExpr;
x_251 = l___private_Init_Util_0__outOfBounds___rarg(x_250);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_252 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_235, x_246, x_251, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = lean_ctor_get(x_253, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_253, 1);
lean_inc(x_256);
lean_dec(x_253);
x_257 = l_Lean_Compiler_LCNF_joinTypes(x_255, x_233);
x_258 = lean_array_push(x_232, x_256);
if (lean_is_scalar(x_234)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_234;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_257);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_236);
lean_ctor_set(x_260, 1, x_259);
if (lean_is_scalar(x_231)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_231;
}
lean_ctor_set(x_261, 0, x_248);
lean_ctor_set(x_261, 1, x_260);
x_262 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_262;
x_7 = x_261;
x_13 = x_254;
goto _start;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_248);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_264 = lean_ctor_get(x_252, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_252, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_266 = x_252;
} else {
 lean_dec_ref(x_252);
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
else
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_array_fget(x_1, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_269 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_235, x_246, x_268, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = lean_ctor_get(x_270, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_270, 1);
lean_inc(x_273);
lean_dec(x_270);
x_274 = l_Lean_Compiler_LCNF_joinTypes(x_272, x_233);
x_275 = lean_array_push(x_232, x_273);
if (lean_is_scalar(x_234)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_234;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_274);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_236);
lean_ctor_set(x_277, 1, x_276);
if (lean_is_scalar(x_231)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_231;
}
lean_ctor_set(x_278, 0, x_248);
lean_ctor_set(x_278, 1, x_277);
x_279 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_279;
x_7 = x_278;
x_13 = x_271;
goto _start;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_248);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_281 = lean_ctor_get(x_269, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_269, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_283 = x_269;
} else {
 lean_dec_ref(x_269);
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
}
}
}
}
else
{
lean_object* x_285; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_7);
lean_ctor_set(x_285, 1, x_13);
return x_285;
}
}
else
{
lean_object* x_286; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_7);
lean_ctor_set(x_286, 1, x_13);
return x_286;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_3, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_3, x_17);
lean_dec(x_3);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_7, 1);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_13);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_22);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_19, 1, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_13);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_7, 0);
lean_inc(x_31);
lean_dec(x_7);
x_32 = lean_ctor_get(x_22, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_34 = x_22;
} else {
 lean_dec_ref(x_22);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_19, 1, x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_19);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_13);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_7);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_19, 1);
x_40 = lean_ctor_get(x_7, 0);
x_41 = lean_ctor_get(x_7, 1);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
x_45 = lean_ctor_get(x_21, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_dec(x_21);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_40, 2);
lean_inc(x_49);
x_50 = lean_nat_dec_lt(x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_ctor_set(x_19, 0, x_46);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_7);
lean_ctor_set(x_51, 1, x_13);
return x_51;
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_40);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_ctor_get(x_40, 2);
lean_dec(x_53);
x_54 = lean_ctor_get(x_40, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_40, 0);
lean_dec(x_55);
x_56 = lean_array_fget(x_47, x_48);
x_57 = lean_nat_add(x_48, x_17);
lean_dec(x_48);
lean_ctor_set(x_40, 1, x_57);
x_58 = lean_nat_dec_lt(x_4, x_2);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = l_Lean_instInhabitedExpr;
x_60 = l___private_Init_Util_0__outOfBounds___rarg(x_59);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_61 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_45, x_56, x_60, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = l_Lean_Compiler_LCNF_joinTypes(x_64, x_44);
x_67 = lean_array_push(x_43, x_65);
lean_ctor_set(x_39, 1, x_66);
lean_ctor_set(x_39, 0, x_67);
lean_ctor_set(x_19, 0, x_46);
x_68 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_68;
x_13 = x_63;
goto _start;
}
else
{
uint8_t x_70; 
lean_dec(x_40);
lean_dec(x_46);
lean_free_object(x_39);
lean_dec(x_44);
lean_dec(x_43);
lean_free_object(x_7);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_61);
if (x_70 == 0)
{
return x_61;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_61, 0);
x_72 = lean_ctor_get(x_61, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_61);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_array_fget(x_1, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_75 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_45, x_56, x_74, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l_Lean_Compiler_LCNF_joinTypes(x_78, x_44);
x_81 = lean_array_push(x_43, x_79);
lean_ctor_set(x_39, 1, x_80);
lean_ctor_set(x_39, 0, x_81);
lean_ctor_set(x_19, 0, x_46);
x_82 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_82;
x_13 = x_77;
goto _start;
}
else
{
uint8_t x_84; 
lean_dec(x_40);
lean_dec(x_46);
lean_free_object(x_39);
lean_dec(x_44);
lean_dec(x_43);
lean_free_object(x_7);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_84 = !lean_is_exclusive(x_75);
if (x_84 == 0)
{
return x_75;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_75, 0);
x_86 = lean_ctor_get(x_75, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_75);
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
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
lean_dec(x_40);
x_88 = lean_array_fget(x_47, x_48);
x_89 = lean_nat_add(x_48, x_17);
lean_dec(x_48);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_47);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_49);
x_91 = lean_nat_dec_lt(x_4, x_2);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = l_Lean_instInhabitedExpr;
x_93 = l___private_Init_Util_0__outOfBounds___rarg(x_92);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_94 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_45, x_88, x_93, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = l_Lean_Compiler_LCNF_joinTypes(x_97, x_44);
x_100 = lean_array_push(x_43, x_98);
lean_ctor_set(x_39, 1, x_99);
lean_ctor_set(x_39, 0, x_100);
lean_ctor_set(x_19, 0, x_46);
lean_ctor_set(x_7, 0, x_90);
x_101 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_101;
x_13 = x_96;
goto _start;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_90);
lean_dec(x_46);
lean_free_object(x_39);
lean_dec(x_44);
lean_dec(x_43);
lean_free_object(x_7);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_103 = lean_ctor_get(x_94, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_94, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_105 = x_94;
} else {
 lean_dec_ref(x_94);
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
x_107 = lean_array_fget(x_1, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_108 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_45, x_88, x_107, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
x_113 = l_Lean_Compiler_LCNF_joinTypes(x_111, x_44);
x_114 = lean_array_push(x_43, x_112);
lean_ctor_set(x_39, 1, x_113);
lean_ctor_set(x_39, 0, x_114);
lean_ctor_set(x_19, 0, x_46);
lean_ctor_set(x_7, 0, x_90);
x_115 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_115;
x_13 = x_110;
goto _start;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_90);
lean_dec(x_46);
lean_free_object(x_39);
lean_dec(x_44);
lean_dec(x_43);
lean_free_object(x_7);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_117 = lean_ctor_get(x_108, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_108, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_119 = x_108;
} else {
 lean_dec_ref(x_108);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_121 = lean_ctor_get(x_39, 0);
x_122 = lean_ctor_get(x_39, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_39);
x_123 = lean_ctor_get(x_21, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_21, 1);
lean_inc(x_124);
lean_dec(x_21);
x_125 = lean_ctor_get(x_40, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_40, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_40, 2);
lean_inc(x_127);
x_128 = lean_nat_dec_lt(x_126, x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_121);
lean_ctor_set(x_129, 1, x_122);
lean_ctor_set(x_19, 1, x_129);
lean_ctor_set(x_19, 0, x_124);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_7);
lean_ctor_set(x_130, 1, x_13);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 x_131 = x_40;
} else {
 lean_dec_ref(x_40);
 x_131 = lean_box(0);
}
x_132 = lean_array_fget(x_125, x_126);
x_133 = lean_nat_add(x_126, x_17);
lean_dec(x_126);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 3, 0);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_134, 2, x_127);
x_135 = lean_nat_dec_lt(x_4, x_2);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = l_Lean_instInhabitedExpr;
x_137 = l___private_Init_Util_0__outOfBounds___rarg(x_136);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_138 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_123, x_132, x_137, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
x_143 = l_Lean_Compiler_LCNF_joinTypes(x_141, x_122);
x_144 = lean_array_push(x_121, x_142);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
lean_ctor_set(x_19, 1, x_145);
lean_ctor_set(x_19, 0, x_124);
lean_ctor_set(x_7, 0, x_134);
x_146 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_146;
x_13 = x_140;
goto _start;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_134);
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_121);
lean_free_object(x_7);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_148 = lean_ctor_get(x_138, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_138, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_150 = x_138;
} else {
 lean_dec_ref(x_138);
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
x_152 = lean_array_fget(x_1, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_153 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_123, x_132, x_152, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec(x_154);
x_158 = l_Lean_Compiler_LCNF_joinTypes(x_156, x_122);
x_159 = lean_array_push(x_121, x_157);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
lean_ctor_set(x_19, 1, x_160);
lean_ctor_set(x_19, 0, x_124);
lean_ctor_set(x_7, 0, x_134);
x_161 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_161;
x_13 = x_155;
goto _start;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_134);
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_121);
lean_free_object(x_7);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_163 = lean_ctor_get(x_153, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_153, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_165 = x_153;
} else {
 lean_dec_ref(x_153);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_167 = lean_ctor_get(x_19, 1);
x_168 = lean_ctor_get(x_7, 0);
lean_inc(x_168);
lean_dec(x_7);
x_169 = lean_ctor_get(x_167, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_171 = x_167;
} else {
 lean_dec_ref(x_167);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_21, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_21, 1);
lean_inc(x_173);
lean_dec(x_21);
x_174 = lean_ctor_get(x_168, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_168, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_168, 2);
lean_inc(x_176);
x_177 = lean_nat_dec_lt(x_175, x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_172);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
if (lean_is_scalar(x_171)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_171;
}
lean_ctor_set(x_178, 0, x_169);
lean_ctor_set(x_178, 1, x_170);
lean_ctor_set(x_19, 1, x_178);
lean_ctor_set(x_19, 0, x_173);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_168);
lean_ctor_set(x_179, 1, x_19);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_13);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 x_181 = x_168;
} else {
 lean_dec_ref(x_168);
 x_181 = lean_box(0);
}
x_182 = lean_array_fget(x_174, x_175);
x_183 = lean_nat_add(x_175, x_17);
lean_dec(x_175);
if (lean_is_scalar(x_181)) {
 x_184 = lean_alloc_ctor(0, 3, 0);
} else {
 x_184 = x_181;
}
lean_ctor_set(x_184, 0, x_174);
lean_ctor_set(x_184, 1, x_183);
lean_ctor_set(x_184, 2, x_176);
x_185 = lean_nat_dec_lt(x_4, x_2);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = l_Lean_instInhabitedExpr;
x_187 = l___private_Init_Util_0__outOfBounds___rarg(x_186);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_188 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_172, x_182, x_187, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_ctor_get(x_189, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
lean_dec(x_189);
x_193 = l_Lean_Compiler_LCNF_joinTypes(x_191, x_170);
x_194 = lean_array_push(x_169, x_192);
if (lean_is_scalar(x_171)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_171;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
lean_ctor_set(x_19, 1, x_195);
lean_ctor_set(x_19, 0, x_173);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_184);
lean_ctor_set(x_196, 1, x_19);
x_197 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_197;
x_7 = x_196;
x_13 = x_190;
goto _start;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_184);
lean_dec(x_173);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_199 = lean_ctor_get(x_188, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_188, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_201 = x_188;
} else {
 lean_dec_ref(x_188);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_array_fget(x_1, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_204 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_172, x_182, x_203, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_ctor_get(x_205, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_208);
lean_dec(x_205);
x_209 = l_Lean_Compiler_LCNF_joinTypes(x_207, x_170);
x_210 = lean_array_push(x_169, x_208);
if (lean_is_scalar(x_171)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_171;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
lean_ctor_set(x_19, 1, x_211);
lean_ctor_set(x_19, 0, x_173);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_184);
lean_ctor_set(x_212, 1, x_19);
x_213 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_213;
x_7 = x_212;
x_13 = x_206;
goto _start;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_184);
lean_dec(x_173);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_215 = lean_ctor_get(x_204, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_204, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_217 = x_204;
} else {
 lean_dec_ref(x_204);
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
}
}
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_19, 1);
x_220 = lean_ctor_get(x_19, 0);
lean_inc(x_219);
lean_inc(x_220);
lean_dec(x_19);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_221 = lean_ctor_get(x_7, 0);
lean_inc(x_221);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_222 = x_7;
} else {
 lean_dec_ref(x_7);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_219, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_219, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_225 = x_219;
} else {
 lean_dec_ref(x_219);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_224);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_220);
lean_ctor_set(x_227, 1, x_226);
if (lean_is_scalar(x_222)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_222;
}
lean_ctor_set(x_228, 0, x_221);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_13);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_230 = lean_ctor_get(x_7, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_231 = x_7;
} else {
 lean_dec_ref(x_7);
 x_231 = lean_box(0);
}
x_232 = lean_ctor_get(x_219, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_219, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_234 = x_219;
} else {
 lean_dec_ref(x_219);
 x_234 = lean_box(0);
}
x_235 = lean_ctor_get(x_220, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_220, 1);
lean_inc(x_236);
lean_dec(x_220);
x_237 = lean_ctor_get(x_230, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_230, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_230, 2);
lean_inc(x_239);
x_240 = lean_nat_dec_lt(x_238, x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_235);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
if (lean_is_scalar(x_234)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_234;
}
lean_ctor_set(x_241, 0, x_232);
lean_ctor_set(x_241, 1, x_233);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_236);
lean_ctor_set(x_242, 1, x_241);
if (lean_is_scalar(x_231)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_231;
}
lean_ctor_set(x_243, 0, x_230);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_13);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 lean_ctor_release(x_230, 2);
 x_245 = x_230;
} else {
 lean_dec_ref(x_230);
 x_245 = lean_box(0);
}
x_246 = lean_array_fget(x_237, x_238);
x_247 = lean_nat_add(x_238, x_17);
lean_dec(x_238);
if (lean_is_scalar(x_245)) {
 x_248 = lean_alloc_ctor(0, 3, 0);
} else {
 x_248 = x_245;
}
lean_ctor_set(x_248, 0, x_237);
lean_ctor_set(x_248, 1, x_247);
lean_ctor_set(x_248, 2, x_239);
x_249 = lean_nat_dec_lt(x_4, x_2);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = l_Lean_instInhabitedExpr;
x_251 = l___private_Init_Util_0__outOfBounds___rarg(x_250);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_252 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_235, x_246, x_251, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = lean_ctor_get(x_253, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_253, 1);
lean_inc(x_256);
lean_dec(x_253);
x_257 = l_Lean_Compiler_LCNF_joinTypes(x_255, x_233);
x_258 = lean_array_push(x_232, x_256);
if (lean_is_scalar(x_234)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_234;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_257);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_236);
lean_ctor_set(x_260, 1, x_259);
if (lean_is_scalar(x_231)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_231;
}
lean_ctor_set(x_261, 0, x_248);
lean_ctor_set(x_261, 1, x_260);
x_262 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_262;
x_7 = x_261;
x_13 = x_254;
goto _start;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_248);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_264 = lean_ctor_get(x_252, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_252, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_266 = x_252;
} else {
 lean_dec_ref(x_252);
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
else
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_array_fget(x_1, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_269 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_235, x_246, x_268, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = lean_ctor_get(x_270, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_270, 1);
lean_inc(x_273);
lean_dec(x_270);
x_274 = l_Lean_Compiler_LCNF_joinTypes(x_272, x_233);
x_275 = lean_array_push(x_232, x_273);
if (lean_is_scalar(x_234)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_234;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_274);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_236);
lean_ctor_set(x_277, 1, x_276);
if (lean_is_scalar(x_231)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_231;
}
lean_ctor_set(x_278, 0, x_248);
lean_ctor_set(x_278, 1, x_277);
x_279 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_279;
x_7 = x_278;
x_13 = x_271;
goto _start;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_248);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_281 = lean_ctor_get(x_269, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_269, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_283 = x_269;
} else {
 lean_dec_ref(x_269);
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
}
}
}
}
else
{
lean_object* x_285; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_7);
lean_ctor_set(x_285, 1, x_13);
return x_285;
}
}
else
{
lean_object* x_286; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_7);
lean_ctor_set(x_286, 1, x_13);
return x_286;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitCases", 43);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__1;
x_3 = lean_unsigned_to_nat(548u);
x_4 = lean_unsigned_to_nat(57u);
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unsupported `", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("` application during code generation", 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Compiler_LCNF_CasesInfo_numAlts(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = l_Lean_Name_getPrefix(x_17);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
x_20 = lean_array_get_size(x_2);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
x_22 = l_Lean_instInhabitedExpr;
x_23 = l___private_Init_Util_0__outOfBounds___rarg(x_22);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_23, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_18);
x_27 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1(x_18, x_5, x_6, x_7, x_8, x_9, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 5)
{
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_17);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_1, 5);
lean_inc(x_33);
x_34 = lean_array_get_size(x_33);
x_35 = l_Array_toSubarray___rarg(x_33, x_15, x_34);
x_36 = lean_ctor_get(x_30, 4);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_ctor_get(x_1, 4);
lean_inc(x_37);
lean_dec(x_1);
x_38 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_12);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 2);
lean_inc(x_44);
lean_dec(x_37);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_42);
x_45 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1(x_2, x_20, x_42, x_43, x_42, x_44, x_41, x_5, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_20);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
lean_inc(x_51);
x_52 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_52, 0, x_18);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_32);
lean_ctor_set(x_52, 3, x_50);
x_53 = 0;
x_54 = l_Lean_Compiler_LCNF_mkAuxParam(x_51, x_53, x_6, x_7, x_8, x_9, x_49);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_55);
x_57 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_52);
x_58 = l_Lean_Compiler_LCNF_ToLCNF_pushElement(x_57, x_5, x_6, x_7, x_8, x_9, x_56);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
lean_dec(x_55);
lean_ctor_set(x_25, 0, x_60);
x_61 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_25, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_59);
lean_dec(x_2);
return x_61;
}
else
{
uint8_t x_62; 
lean_free_object(x_25);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_45);
if (x_62 == 0)
{
return x_45;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_45, 0);
x_64 = lean_ctor_get(x_45, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_45);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_66 = lean_ctor_get(x_25, 0);
lean_inc(x_66);
lean_dec(x_25);
x_67 = lean_ctor_get(x_1, 5);
lean_inc(x_67);
x_68 = lean_array_get_size(x_67);
x_69 = l_Array_toSubarray___rarg(x_67, x_15, x_68);
x_70 = lean_ctor_get(x_30, 4);
lean_inc(x_70);
lean_dec(x_30);
x_71 = lean_ctor_get(x_1, 4);
lean_inc(x_71);
lean_dec(x_1);
x_72 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_12);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_ctor_get(x_71, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_71, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 2);
lean_inc(x_78);
lean_dec(x_71);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_76);
x_79 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1(x_2, x_20, x_76, x_77, x_76, x_78, x_75, x_5, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_20);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
lean_inc(x_85);
x_86 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_86, 0, x_18);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_66);
lean_ctor_set(x_86, 3, x_84);
x_87 = 0;
x_88 = l_Lean_Compiler_LCNF_mkAuxParam(x_85, x_87, x_6, x_7, x_8, x_9, x_83);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
lean_inc(x_89);
x_91 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_86);
x_92 = l_Lean_Compiler_LCNF_ToLCNF_pushElement(x_91, x_5, x_6, x_7, x_8, x_9, x_90);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
lean_dec(x_89);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_95, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_93);
lean_dec(x_2);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_66);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_97 = lean_ctor_get(x_79, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_79, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_99 = x_79;
} else {
 lean_dec_ref(x_79);
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
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = lean_ctor_get(x_27, 1);
lean_inc(x_101);
lean_dec(x_27);
x_102 = l_Lean_MessageData_ofName(x_17);
x_103 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__4;
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__6;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___spec__1(x_106, x_5, x_6, x_7, x_8, x_9, x_101);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = lean_ctor_get(x_27, 1);
lean_inc(x_108);
lean_dec(x_27);
x_109 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__2;
x_110 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_109, x_5, x_6, x_7, x_8, x_9, x_108);
return x_110;
}
}
else
{
uint8_t x_111; 
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_27);
if (x_111 == 0)
{
return x_27;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_27, 0);
x_113 = lean_ctor_get(x_27, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_27);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_24);
if (x_115 == 0)
{
return x_24;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_24, 0);
x_117 = lean_ctor_get(x_24, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_24);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_array_fget(x_2, x_19);
lean_dec(x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_120 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_119, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
lean_inc(x_18);
x_123 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1(x_18, x_5, x_6, x_7, x_8, x_9, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 5)
{
if (lean_obj_tag(x_121) == 1)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_dec(x_17);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
lean_dec(x_124);
x_127 = !lean_is_exclusive(x_121);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_128 = lean_ctor_get(x_121, 0);
x_129 = lean_ctor_get(x_1, 5);
lean_inc(x_129);
x_130 = lean_array_get_size(x_129);
x_131 = l_Array_toSubarray___rarg(x_129, x_15, x_130);
x_132 = lean_ctor_get(x_126, 4);
lean_inc(x_132);
lean_dec(x_126);
x_133 = lean_ctor_get(x_1, 4);
lean_inc(x_133);
lean_dec(x_1);
x_134 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_12);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_132);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_131);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_133, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_133, 2);
lean_inc(x_140);
lean_dec(x_133);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_138);
x_141 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__2(x_2, x_20, x_138, x_139, x_138, x_140, x_137, x_5, x_6, x_7, x_8, x_9, x_125);
lean_dec(x_140);
lean_dec(x_138);
lean_dec(x_20);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
lean_dec(x_143);
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
lean_dec(x_141);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
lean_inc(x_147);
x_148 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_148, 0, x_18);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_148, 2, x_128);
lean_ctor_set(x_148, 3, x_146);
x_149 = 0;
x_150 = l_Lean_Compiler_LCNF_mkAuxParam(x_147, x_149, x_6, x_7, x_8, x_9, x_145);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
lean_inc(x_151);
x_153 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_148);
x_154 = l_Lean_Compiler_LCNF_ToLCNF_pushElement(x_153, x_5, x_6, x_7, x_8, x_9, x_152);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_ctor_get(x_151, 0);
lean_inc(x_156);
lean_dec(x_151);
lean_ctor_set(x_121, 0, x_156);
x_157 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_121, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_155);
lean_dec(x_2);
return x_157;
}
else
{
uint8_t x_158; 
lean_free_object(x_121);
lean_dec(x_128);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_158 = !lean_is_exclusive(x_141);
if (x_158 == 0)
{
return x_141;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_141, 0);
x_160 = lean_ctor_get(x_141, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_141);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_162 = lean_ctor_get(x_121, 0);
lean_inc(x_162);
lean_dec(x_121);
x_163 = lean_ctor_get(x_1, 5);
lean_inc(x_163);
x_164 = lean_array_get_size(x_163);
x_165 = l_Array_toSubarray___rarg(x_163, x_15, x_164);
x_166 = lean_ctor_get(x_126, 4);
lean_inc(x_166);
lean_dec(x_126);
x_167 = lean_ctor_get(x_1, 4);
lean_inc(x_167);
lean_dec(x_1);
x_168 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_12);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_166);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_165);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_ctor_get(x_167, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_167, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_167, 2);
lean_inc(x_174);
lean_dec(x_167);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_172);
x_175 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__2(x_2, x_20, x_172, x_173, x_172, x_174, x_171, x_5, x_6, x_7, x_8, x_9, x_125);
lean_dec(x_174);
lean_dec(x_172);
lean_dec(x_20);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
x_179 = lean_ctor_get(x_175, 1);
lean_inc(x_179);
lean_dec(x_175);
x_180 = lean_ctor_get(x_178, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_181);
lean_dec(x_178);
lean_inc(x_181);
x_182 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_182, 0, x_18);
lean_ctor_set(x_182, 1, x_181);
lean_ctor_set(x_182, 2, x_162);
lean_ctor_set(x_182, 3, x_180);
x_183 = 0;
x_184 = l_Lean_Compiler_LCNF_mkAuxParam(x_181, x_183, x_6, x_7, x_8, x_9, x_179);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
lean_inc(x_185);
x_187 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_182);
x_188 = l_Lean_Compiler_LCNF_ToLCNF_pushElement(x_187, x_5, x_6, x_7, x_8, x_9, x_186);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
x_190 = lean_ctor_get(x_185, 0);
lean_inc(x_190);
lean_dec(x_185);
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_190);
x_192 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_191, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_189);
lean_dec(x_2);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_162);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_193 = lean_ctor_get(x_175, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_175, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_195 = x_175;
} else {
 lean_dec_ref(x_175);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_124);
lean_dec(x_121);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_197 = lean_ctor_get(x_123, 1);
lean_inc(x_197);
lean_dec(x_123);
x_198 = l_Lean_MessageData_ofName(x_17);
x_199 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__4;
x_200 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_198);
x_201 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__6;
x_202 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_203 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___spec__1(x_202, x_5, x_6, x_7, x_8, x_9, x_197);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_124);
lean_dec(x_121);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_204 = lean_ctor_get(x_123, 1);
lean_inc(x_204);
lean_dec(x_123);
x_205 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__2;
x_206 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_205, x_5, x_6, x_7, x_8, x_9, x_204);
return x_206;
}
}
else
{
uint8_t x_207; 
lean_dec(x_121);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_207 = !lean_is_exclusive(x_123);
if (x_207 == 0)
{
return x_123;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_123, 0);
x_209 = lean_ctor_get(x_123, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_123);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_211 = !lean_is_exclusive(x_120);
if (x_211 == 0)
{
return x_120;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_120, 0);
x_213 = lean_ctor_get(x_120, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_120);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
}
else
{
lean_object* x_215; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_215 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_12, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_215;
}
}
else
{
uint8_t x_216; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_216 = !lean_is_exclusive(x_11);
if (x_216 == 0)
{
return x_11;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_11, 0);
x_218 = lean_ctor_get(x_11, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_11);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_10);
x_12 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_11);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_11, x_14);
lean_dec(x_11);
lean_inc(x_2);
x_16 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_13, x_15);
x_17 = l_Lean_Expr_getAppFn(x_2);
lean_inc(x_9);
lean_inc(x_16);
x_18 = l_Array_toSubarray___rarg(x_16, x_10, x_9);
x_19 = l_Array_ofSubarray___rarg(x_18);
x_20 = l_Lean_mkAppN(x_17, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___boxed), 7, 1);
lean_closure_set(x_22, 0, x_21);
lean_inc(x_9);
x_23 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1), 10, 3);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_16);
lean_closure_set(x_23, 2, x_9);
x_24 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
x_25 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_2, x_9, x_24, x_3, x_4, x_5, x_6, x_7, x_8);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_3, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_3, x_17);
lean_dec(x_3);
x_19 = lean_nat_dec_lt(x_4, x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_instInhabitedExpr;
x_21 = l___private_Init_Util_0__outOfBounds___rarg(x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_21, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_push(x_7, x_23);
x_26 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_26;
x_7 = x_25;
x_13 = x_24;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_array_fget(x_1, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_33 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_32, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_array_push(x_7, x_34);
x_37 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_37;
x_7 = x_36;
x_13 = x_35;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
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
}
else
{
lean_object* x_43; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_7);
lean_ctor_set(x_43, 1, x_13);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_7);
lean_ctor_set(x_44, 1, x_13);
return x_44;
}
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
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_15 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___spec__1(x_2, x_10, x_10, x_3, x_10, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
x_20 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_18, x_19, x_4, x_5, x_6, x_7, x_8, x_17);
lean_dec(x_4);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_9);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny(x_9, x_3, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(x_1, x_11, x_4, x_5, x_6, x_7, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
lean_inc(x_12);
x_15 = l_Lean_Compiler_LCNF_Param_toExpr(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Compiler_LCNF_inferType(x_15, x_5, x_6, x_7, x_8, x_9);
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
lean_inc(x_4);
x_19 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(x_17, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1___lambda__1(x_12, x_23, x_4, x_5, x_6, x_7, x_8, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = 1;
x_28 = lean_usize_add(x_2, x_27);
x_29 = lean_array_uset(x_14, x_2, x_25);
x_2 = x_28;
x_3 = x_29;
x_9 = x_26;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_st_ref_take(x_4, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; 
x_36 = lean_ctor_get(x_33, 5);
x_37 = lean_ctor_get(x_12, 0);
lean_inc(x_37);
x_38 = lean_box(0);
x_39 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_36, x_37, x_38);
lean_ctor_set(x_33, 5, x_39);
x_40 = lean_st_ref_set(x_4, x_33, x_34);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1___lambda__1(x_12, x_38, x_4, x_5, x_6, x_7, x_8, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = 1;
x_46 = lean_usize_add(x_2, x_45);
x_47 = lean_array_uset(x_14, x_2, x_43);
x_2 = x_46;
x_3 = x_47;
x_9 = x_44;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; 
x_49 = lean_ctor_get(x_33, 0);
x_50 = lean_ctor_get(x_33, 1);
x_51 = lean_ctor_get(x_33, 2);
x_52 = lean_ctor_get(x_33, 3);
x_53 = lean_ctor_get(x_33, 4);
x_54 = lean_ctor_get(x_33, 5);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_33);
x_55 = lean_ctor_get(x_12, 0);
lean_inc(x_55);
x_56 = lean_box(0);
x_57 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_54, x_55, x_56);
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_49);
lean_ctor_set(x_58, 1, x_50);
lean_ctor_set(x_58, 2, x_51);
lean_ctor_set(x_58, 3, x_52);
lean_ctor_set(x_58, 4, x_53);
lean_ctor_set(x_58, 5, x_57);
x_59 = lean_st_ref_set(x_4, x_58, x_34);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1___lambda__1(x_12, x_56, x_4, x_5, x_6, x_7, x_8, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = 1;
x_65 = lean_usize_add(x_2, x_64);
x_66 = lean_array_uset(x_14, x_2, x_62);
x_2 = x_65;
x_3 = x_66;
x_9 = x_63;
goto _start;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_68 = !lean_is_exclusive(x_19);
if (x_68 == 0)
{
return x_19;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_19, 0);
x_70 = lean_ctor_get(x_19, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_19);
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
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_72 = !lean_is_exclusive(x_16);
if (x_72 == 0)
{
return x_16;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_16, 0);
x_74 = lean_ctor_get(x_16, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_16);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1(x_12, x_13, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_17 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_2, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_toCode(x_18, x_5, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_5);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_21);
x_23 = l_Lean_Compiler_LCNF_Code_inferType(x_21, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set(x_26, 2, x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
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
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_15);
lean_ctor_set(x_30, 2, x_21);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_1);
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
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_17);
if (x_41 == 0)
{
return x_17;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_17, 0);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_17);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_lt(x_12, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__1(x_1, x_11, x_10, x_14, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_nat_sub(x_2, x_12);
lean_dec(x_12);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(x_11, x_16, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda(x_18, x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Array_append___rarg(x_10, x_23);
x_26 = lean_box(0);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__1(x_1, x_24, x_25, x_26, x_4, x_5, x_6, x_7, x_8, x_22);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___boxed), 8, 2);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__2), 9, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___rarg(x_12, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___boxed), 7, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___closed__1;
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_12, x_11, x_2, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___closed__1() {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_9);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_10);
x_12 = lean_mk_array(x_10, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_10, x_13);
lean_dec(x_10);
lean_inc(x_1);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_12, x_14);
x_16 = lean_array_get_size(x_15);
x_17 = lean_nat_dec_lt(x_9, x_16);
x_18 = lean_nat_dec_lt(x_13, x_16);
x_19 = lean_nat_dec_lt(x_2, x_16);
lean_dec(x_16);
x_20 = lean_array_get_size(x_15);
x_21 = lean_unsigned_to_nat(5u);
lean_inc(x_15);
x_22 = l_Array_toSubarray___rarg(x_15, x_21, x_20);
x_23 = l_Array_ofSubarray___rarg(x_22);
if (x_17 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_instInhabitedExpr;
x_58 = l___private_Init_Util_0__outOfBounds___rarg(x_57);
x_24 = x_58;
goto block_56;
}
else
{
lean_object* x_59; 
x_59 = lean_array_fget(x_15, x_9);
x_24 = x_59;
goto block_56;
}
block_56:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(x_24);
x_26 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___closed__1;
x_27 = lean_array_push(x_26, x_25);
if (x_18 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = l_Lean_instInhabitedExpr;
x_29 = l___private_Init_Util_0__outOfBounds___rarg(x_28);
x_30 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(x_29);
x_31 = lean_array_push(x_27, x_30);
if (x_19 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_15);
lean_dec(x_2);
x_32 = l___private_Init_Util_0__outOfBounds___rarg(x_28);
x_33 = l_Lean_Expr_beta(x_32, x_31);
x_34 = l_Lean_mkAppN(x_33, x_23);
x_35 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 7, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_21, x_35, x_3, x_4, x_5, x_6, x_7, x_8);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_array_fget(x_15, x_2);
lean_dec(x_2);
lean_dec(x_15);
x_38 = l_Lean_Expr_beta(x_37, x_31);
x_39 = l_Lean_mkAppN(x_38, x_23);
x_40 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 7, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_21, x_40, x_3, x_4, x_5, x_6, x_7, x_8);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_array_fget(x_15, x_13);
x_43 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(x_42);
x_44 = lean_array_push(x_27, x_43);
if (x_19 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_15);
lean_dec(x_2);
x_45 = l_Lean_instInhabitedExpr;
x_46 = l___private_Init_Util_0__outOfBounds___rarg(x_45);
x_47 = l_Lean_Expr_beta(x_46, x_44);
x_48 = l_Lean_mkAppN(x_47, x_23);
x_49 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 7, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_21, x_49, x_3, x_4, x_5, x_6, x_7, x_8);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_array_fget(x_15, x_2);
lean_dec(x_2);
lean_dec(x_15);
x_52 = l_Lean_Expr_beta(x_51, x_44);
x_53 = l_Lean_mkAppN(x_52, x_23);
x_54 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 7, 1);
lean_closure_set(x_54, 0, x_53);
x_55 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_21, x_54, x_3, x_4, x_5, x_6, x_7, x_8);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(6u);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_2, x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_8);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_9);
x_11 = lean_mk_array(x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_9, x_12);
lean_dec(x_9);
lean_inc(x_1);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_11, x_13);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10;
x_16 = l_Lean_Expr_isAppOf(x_1, x_15);
lean_inc(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___lambda__1), 8, 1);
lean_closure_set(x_17, 0, x_14);
if (x_16 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__5;
x_19 = l_Lean_Expr_isAppOf(x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_array_get_size(x_14);
x_21 = lean_unsigned_to_nat(5u);
x_22 = lean_nat_dec_lt(x_21, x_20);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_14);
x_23 = l_Lean_instInhabitedExpr;
x_24 = l___private_Init_Util_0__outOfBounds___rarg(x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 7, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_17);
x_27 = lean_unsigned_to_nat(6u);
x_28 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_27, x_26, x_2, x_3, x_4, x_5, x_6, x_7);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_array_fget(x_14, x_21);
lean_dec(x_14);
x_30 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 7, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_31, 0, x_30);
lean_closure_set(x_31, 1, x_17);
x_32 = lean_unsigned_to_nat(6u);
x_33 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_32, x_31, x_2, x_3, x_4, x_5, x_6, x_7);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_array_get_size(x_14);
x_35 = lean_unsigned_to_nat(3u);
x_36 = lean_nat_dec_lt(x_35, x_34);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_14);
x_37 = l_Lean_instInhabitedExpr;
x_38 = l___private_Init_Util_0__outOfBounds___rarg(x_37);
x_39 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 7, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_40, 0, x_39);
lean_closure_set(x_40, 1, x_17);
x_41 = lean_unsigned_to_nat(6u);
x_42 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_41, x_40, x_2, x_3, x_4, x_5, x_6, x_7);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_array_fget(x_14, x_35);
lean_dec(x_14);
x_44 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 7, 1);
lean_closure_set(x_44, 0, x_43);
x_45 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_45, 0, x_44);
lean_closure_set(x_45, 1, x_17);
x_46 = lean_unsigned_to_nat(6u);
x_47 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_46, x_45, x_2, x_3, x_4, x_5, x_6, x_7);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_array_get_size(x_14);
x_49 = lean_unsigned_to_nat(3u);
x_50 = lean_nat_dec_lt(x_49, x_48);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_14);
x_51 = l_Lean_instInhabitedExpr;
x_52 = l___private_Init_Util_0__outOfBounds___rarg(x_51);
x_53 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 7, 1);
lean_closure_set(x_53, 0, x_52);
x_54 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_54, 0, x_53);
lean_closure_set(x_54, 1, x_17);
x_55 = lean_unsigned_to_nat(6u);
x_56 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_55, x_54, x_2, x_3, x_4, x_5, x_6, x_7);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_array_fget(x_14, x_49);
lean_dec(x_14);
x_58 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 7, 1);
lean_closure_set(x_58, 0, x_57);
x_59 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_59, 0, x_58);
lean_closure_set(x_59, 1, x_17);
x_60 = lean_unsigned_to_nat(6u);
x_61 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_60, x_59, x_2, x_3, x_4, x_5, x_6, x_7);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lean_Expr_getAppFn(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_10);
x_12 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_11);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_11, x_14);
lean_dec(x_11);
lean_inc(x_2);
x_16 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_13, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst), 8, 2);
lean_closure_set(x_17, 0, x_9);
lean_closure_set(x_17, 1, x_16);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_2, x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.ToLCNF.toLCNF.visitQuotLift", 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__1;
x_3 = lean_unsigned_to_nat(579u);
x_4 = lean_unsigned_to_nat(42u);
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lcInv", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__1;
x_3 = lean_unsigned_to_nat(583u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_135; uint8_t x_136; 
x_135 = lean_unsigned_to_nat(5u);
x_136 = lean_nat_dec_lt(x_135, x_5);
lean_dec(x_5);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = l_Lean_instInhabitedExpr;
x_138 = l___private_Init_Util_0__outOfBounds___rarg(x_137);
x_13 = x_138;
goto block_134;
}
else
{
lean_object* x_139; 
x_139 = lean_array_fget(x_4, x_135);
x_13 = x_139;
goto block_134;
}
block_134:
{
lean_object* x_14; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_13, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_17) == 4)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2;
x_20 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_19, x_7, x_8, x_9, x_10, x_11, x_16);
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
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2;
x_23 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_22, x_7, x_8, x_9, x_10, x_11, x_16);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 1);
x_26 = lean_ctor_get(x_21, 0);
lean_dec(x_26);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_box(0);
lean_ctor_set(x_21, 1, x_28);
lean_ctor_set(x_21, 0, x_27);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_2);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_3);
x_31 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__5;
x_32 = lean_array_push(x_31, x_29);
x_33 = lean_array_push(x_32, x_30);
x_34 = lean_array_push(x_33, x_15);
x_35 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__4;
x_36 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_21);
lean_ctor_set(x_36, 2, x_34);
x_37 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_38 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_36, x_37, x_7, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_38) == 0)
{
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_39; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
case 1:
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_dec(x_38);
x_47 = !lean_is_exclusive(x_6);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_6, 0);
lean_ctor_set(x_6, 0, x_45);
x_49 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5;
x_50 = lean_array_push(x_49, x_6);
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_52 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_51, x_37, x_7, x_8, x_9, x_10, x_11, x_46);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_unsigned_to_nat(6u);
x_56 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_53, x_4, x_55, x_7, x_8, x_9, x_10, x_11, x_54);
lean_dec(x_4);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_6, 0);
lean_inc(x_61);
lean_dec(x_6);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_45);
x_63 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5;
x_64 = lean_array_push(x_63, x_62);
x_65 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_64);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_66 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_65, x_37, x_7, x_8, x_9, x_10, x_11, x_46);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unsigned_to_nat(6u);
x_70 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_67, x_4, x_69, x_7, x_8, x_9, x_10, x_11, x_68);
lean_dec(x_4);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_73 = x_66;
} else {
 lean_dec_ref(x_66);
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
default: 
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_6);
lean_dec(x_4);
x_75 = lean_ctor_get(x_38, 1);
lean_inc(x_75);
lean_dec(x_38);
x_76 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__6;
x_77 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_76, x_7, x_8, x_9, x_10, x_11, x_75);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_78 = !lean_is_exclusive(x_38);
if (x_78 == 0)
{
return x_38;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_38, 0);
x_80 = lean_ctor_get(x_38, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_38);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_free_object(x_21);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2;
x_83 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_82, x_7, x_8, x_9, x_10, x_11, x_16);
return x_83;
}
}
else
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_21, 1);
lean_inc(x_84);
lean_dec(x_21);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_85 = lean_ctor_get(x_18, 0);
lean_inc(x_85);
lean_dec(x_18);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_88, 0, x_2);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_3);
x_90 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__5;
x_91 = lean_array_push(x_90, x_88);
x_92 = lean_array_push(x_91, x_89);
x_93 = lean_array_push(x_92, x_15);
x_94 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__4;
x_95 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_87);
lean_ctor_set(x_95, 2, x_93);
x_96 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_97 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_95, x_96, x_7, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_97) == 0)
{
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
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
x_100 = lean_box(0);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
case 1:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_102 = lean_ctor_get(x_97, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_97, 1);
lean_inc(x_103);
lean_dec(x_97);
x_104 = lean_ctor_get(x_6, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_105 = x_6;
} else {
 lean_dec_ref(x_6);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_102);
x_107 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5;
x_108 = lean_array_push(x_107, x_106);
x_109 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_108);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_110 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_109, x_96, x_7, x_8, x_9, x_10, x_11, x_103);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_unsigned_to_nat(6u);
x_114 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_111, x_4, x_113, x_7, x_8, x_9, x_10, x_11, x_112);
lean_dec(x_4);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_115 = lean_ctor_get(x_110, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_110, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_117 = x_110;
} else {
 lean_dec_ref(x_110);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
default: 
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_6);
lean_dec(x_4);
x_119 = lean_ctor_get(x_97, 1);
lean_inc(x_119);
lean_dec(x_97);
x_120 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__6;
x_121 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_120, x_7, x_8, x_9, x_10, x_11, x_119);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_122 = lean_ctor_get(x_97, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_97, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_124 = x_97;
} else {
 lean_dec_ref(x_97);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_84);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_126 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2;
x_127 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_126, x_7, x_8, x_9, x_10, x_11, x_16);
return x_127;
}
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_128 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2;
x_129 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_128, x_7, x_8, x_9, x_10, x_11, x_16);
return x_129;
}
}
else
{
uint8_t x_130; 
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
x_130 = !lean_is_exclusive(x_14);
if (x_130 == 0)
{
return x_14;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_14, 0);
x_132 = lean_ctor_get(x_14, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_14);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_8);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_9);
x_11 = lean_mk_array(x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_9, x_12);
lean_dec(x_9);
lean_inc(x_1);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_11, x_13);
x_15 = lean_array_get_size(x_14);
x_16 = lean_nat_dec_lt(x_8, x_15);
x_17 = lean_nat_dec_lt(x_12, x_15);
x_18 = lean_unsigned_to_nat(3u);
x_19 = lean_nat_dec_lt(x_18, x_15);
if (x_16 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_instInhabitedExpr;
x_40 = l___private_Init_Util_0__outOfBounds___rarg(x_39);
x_20 = x_40;
goto block_38;
}
else
{
lean_object* x_41; 
x_41 = lean_array_fget(x_14, x_8);
x_20 = x_41;
goto block_38;
}
block_38:
{
lean_object* x_21; 
if (x_17 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_instInhabitedExpr;
x_36 = l___private_Init_Util_0__outOfBounds___rarg(x_35);
x_21 = x_36;
goto block_34;
}
else
{
lean_object* x_37; 
x_37 = lean_array_fget(x_14, x_12);
x_21 = x_37;
goto block_34;
}
block_34:
{
lean_object* x_22; 
lean_inc(x_14);
lean_inc(x_1);
x_22 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1), 12, 5);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_20);
lean_closure_set(x_22, 2, x_21);
lean_closure_set(x_22, 3, x_14);
lean_closure_set(x_22, 4, x_15);
if (x_19 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_14);
x_23 = l_Lean_instInhabitedExpr;
x_24 = l___private_Init_Util_0__outOfBounds___rarg(x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg), 7, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_22);
x_27 = lean_unsigned_to_nat(6u);
x_28 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_27, x_26, x_2, x_3, x_4, x_5, x_6, x_7);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_array_fget(x_14, x_18);
lean_dec(x_14);
x_30 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg), 7, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_31, 0, x_30);
lean_closure_set(x_31, 1, x_22);
x_32 = lean_unsigned_to_nat(6u);
x_33 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_32, x_31, x_2, x_3, x_4, x_5, x_6, x_7);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__3(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__8(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__7(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__1(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toCode___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF___closed__1;
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_run___rarg(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ProjFns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_BorrowedAnnotation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ToLCNF(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ProjFns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_BorrowedAnnotation(builtin, lean_io_mk_world());
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
l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__1);
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
l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement = _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement);
l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__1 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__1();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__1);
l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__2 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__2();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__2);
l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__3 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__3();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__3);
l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__4 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__4();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__4);
l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__5 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__5();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__5);
l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__6 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__6();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___closed__6);
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
l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__4 = _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__4);
l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__5 = _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__5);
l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default = _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default);
l_Lean_Compiler_LCNF_ToLCNF_State_cache___default___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_State_cache___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_State_cache___default___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_State_cache___default = _init_l_Lean_Compiler_LCNF_ToLCNF_State_cache___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_State_cache___default);
l_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default = _init_l_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default);
l_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default = _init_l_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default);
l_Lean_Compiler_LCNF_ToLCNF_State_seq___default = _init_l_Lean_Compiler_LCNF_ToLCNF_State_seq___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_State_seq___default);
l_Lean_Compiler_LCNF_ToLCNF_State_toAny___default = _init_l_Lean_Compiler_LCNF_ToLCNF_State_toAny___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_State_toAny___default);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__4 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__4);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__5 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__5);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__6 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__6);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__7 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__7);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__8 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__8);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__9 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__9);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__10 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__10);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__11 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__11);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__12 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__12);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__13 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__13);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__14 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__14);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__15 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__15);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__16 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__16);
l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__17 = _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__17);
l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__4 = _init_l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__4);
l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__5 = _init_l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__5);
l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__1();
l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__3 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__3();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__3);
l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__1);
l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__2 = _init_l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__2);
l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__4 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__4);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___closed__1);
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
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__2);
l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__1 = _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__1);
l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__2 = _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__2);
l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__3 = _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__3();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__3);
l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__4 = _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__4();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__4);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__4 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__4);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__4 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__4);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__5 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__5);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__6 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__6);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__4 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__4);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__5 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__5);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__6 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__6);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
