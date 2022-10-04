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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_toAny___default;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Compiler_LCNF_anyTypeExpr;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__9;
uint8_t lean_is_marked_borrowed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_mkLcCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__6;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__4;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__1;
extern lean_object* l_Lean_noConfusionExt;
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__2;
lean_object* l_Lean_Compiler_LCNF_mkParam(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13;
lean_object* l_Lean_Compiler_LCNF_CasesInfo_numAlts(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_cache___default___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__2___boxed(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2;
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__4;
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement;
lean_object* l_Lean_Compiler_LCNF_eraseParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__8___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_isLCProof(lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__4;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Param_toExpr(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__6;
lean_object* l_Lean_Meta_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___lambda__1___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__2;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__1(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default___spec__1___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__3;
lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Compiler_LCNF_ToLCNF_bindCases___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11;
uint8_t l_Lean_RBNode_isBlack___rarg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_appendTrees___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__16;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Compiler_LCNF_ToLCNF_etaExpandN___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedProjectionFunctionInfo;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___closed__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instHashableExpr;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17;
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8;
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__3;
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__8(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___closed__1;
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__3(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isPredicateType(lean_object*);
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__3;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default___spec__1___boxed(lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10___closed__2;
size_t lean_usize_modn(size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at_Lean_Compiler_LCNF_CompilerM_codeBind_go___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getCasesInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__3;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__4;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__3;
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2;
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___spec__2(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectExpr___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1;
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_toCtorIfLit(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Compiler_LCNF_ToLCNF_bindCases___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
extern lean_object* l_Lean_projectionFnInfoExt;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_builtinRuntimeTypes;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__5;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1;
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__2;
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Compiler_LCNF_ToLCNF_etaExpandN___spec__1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__6;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__3___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__4;
extern lean_object* l_Lean_Core_instMonadCoreM;
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__3;
uint8_t l_Lean_RBNode_isRed___rarg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_compatibleTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__3(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getCtorArity_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__5;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__5;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__8;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1;
static size_t l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__1;
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM(lean_object*);
lean_object* l_Lean_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MapDeclarationExtension_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__7(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__13;
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_390_(uint8_t, uint8_t);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10___closed__1;
extern lean_object* l_Lean_Expr_instBEqExpr;
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__14;
static lean_object* l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__4;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__2;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__18;
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__8___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__3;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__1;
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__3;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__2;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_cache___default;
lean_object* l_Lean_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__3;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5;
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__3;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndRec___closed__1;
lean_object* l_Lean_Expr_isConstructorApp_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__1;
static size_t l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_seq___default;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__7;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__9;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default___spec__1(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_10 = l_Lean_Compiler_LCNF_findLetDecl_x3f(x_1, x_2, x_3, x_4, x_5, x_9);
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
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_1 = x_21;
x_6 = x_20;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_19);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_10, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_10, 0, x_25);
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_7);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_7, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
return x_7;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_8, 0);
lean_inc(x_32);
lean_dec(x_8);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_7, 0, x_33);
return x_7;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_dec(x_7);
x_35 = lean_ctor_get(x_8, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_36 = x_8;
} else {
 lean_dec_ref(x_8);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 1, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
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
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; 
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
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lean_Expr_fvar___override(x_29);
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
lean_dec(x_14);
lean_inc(x_30);
x_32 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_18, x_31, x_30);
x_33 = lean_array_push(x_15, x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = 1;
x_37 = lean_usize_add(x_3, x_36);
x_3 = x_37;
x_4 = x_35;
x_10 = x_27;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_13 = l_Lean_Name_quickCmp(x_2, x_10);
switch (x_13) {
case 0:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_RBNode_ins___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__6(x_9, x_2, x_3);
x_15 = 0;
lean_ctor_set(x_1, 0, x_14);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
case 1:
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
default: 
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_RBNode_ins___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__6(x_12, x_2, x_3);
x_18 = 0;
lean_ctor_set(x_1, 3, x_17);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_18);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_23 = l_Lean_Name_quickCmp(x_2, x_20);
switch (x_23) {
case 0:
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = l_Lean_RBNode_ins___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__6(x_19, x_2, x_3);
x_25 = 0;
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_25);
return x_26;
}
case 1:
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
default: 
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = l_Lean_RBNode_ins___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__6(x_22, x_2, x_3);
x_30 = 0;
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 2);
x_36 = lean_ctor_get(x_1, 3);
x_37 = l_Lean_Name_quickCmp(x_2, x_34);
switch (x_37) {
case 0:
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_RBNode_ins___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__6(x_33, x_2, x_3);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*4);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_38, 3);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_38, 3);
lean_dec(x_43);
x_44 = lean_ctor_get(x_38, 0);
lean_dec(x_44);
lean_ctor_set(x_38, 0, x_41);
x_45 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_38, 1);
x_47 = lean_ctor_get(x_38, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_39);
x_49 = 1;
lean_ctor_set(x_1, 0, x_48);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_41, sizeof(void*)*4);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_38, 1);
x_53 = lean_ctor_get(x_38, 2);
x_54 = lean_ctor_get(x_38, 3);
lean_dec(x_54);
x_55 = lean_ctor_get(x_38, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_41);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_41, 0);
x_58 = lean_ctor_get(x_41, 1);
x_59 = lean_ctor_get(x_41, 2);
x_60 = lean_ctor_get(x_41, 3);
x_61 = 1;
lean_ctor_set(x_41, 3, x_57);
lean_ctor_set(x_41, 2, x_53);
lean_ctor_set(x_41, 1, x_52);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_61);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_60);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_61);
x_62 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_59);
lean_ctor_set(x_1, 1, x_58);
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_62);
return x_1;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; uint8_t x_69; 
x_63 = lean_ctor_get(x_41, 0);
x_64 = lean_ctor_get(x_41, 1);
x_65 = lean_ctor_get(x_41, 2);
x_66 = lean_ctor_get(x_41, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_41);
x_67 = 1;
x_68 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_68, 0, x_40);
lean_ctor_set(x_68, 1, x_52);
lean_ctor_set(x_68, 2, x_53);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set_uint8(x_68, sizeof(void*)*4, x_67);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_66);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_67);
x_69 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_65);
lean_ctor_set(x_1, 1, x_64);
lean_ctor_set(x_1, 0, x_68);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_70 = lean_ctor_get(x_38, 1);
x_71 = lean_ctor_get(x_38, 2);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_38);
x_72 = lean_ctor_get(x_41, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_41, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_41, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_41, 3);
lean_inc(x_75);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_76 = x_41;
} else {
 lean_dec_ref(x_41);
 x_76 = lean_box(0);
}
x_77 = 1;
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(1, 4, 1);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_40);
lean_ctor_set(x_78, 1, x_70);
lean_ctor_set(x_78, 2, x_71);
lean_ctor_set(x_78, 3, x_72);
lean_ctor_set_uint8(x_78, sizeof(void*)*4, x_77);
x_79 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_34);
lean_ctor_set(x_79, 2, x_35);
lean_ctor_set(x_79, 3, x_36);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_77);
x_80 = 0;
lean_ctor_set(x_1, 3, x_79);
lean_ctor_set(x_1, 2, x_74);
lean_ctor_set(x_1, 1, x_73);
lean_ctor_set(x_1, 0, x_78);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_80);
return x_1;
}
}
else
{
uint8_t x_81; 
lean_free_object(x_1);
x_81 = !lean_is_exclusive(x_41);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_41, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_41, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_41, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_41, 0);
lean_dec(x_85);
x_86 = 1;
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_86);
return x_41;
}
else
{
uint8_t x_87; lean_object* x_88; 
lean_dec(x_41);
x_87 = 1;
x_88 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_88, 0, x_38);
lean_ctor_set(x_88, 1, x_34);
lean_ctor_set(x_88, 2, x_35);
lean_ctor_set(x_88, 3, x_36);
lean_ctor_set_uint8(x_88, sizeof(void*)*4, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
x_89 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_38);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_91 = lean_ctor_get(x_38, 1);
x_92 = lean_ctor_get(x_38, 2);
x_93 = lean_ctor_get(x_38, 3);
x_94 = lean_ctor_get(x_38, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_40);
if (x_95 == 0)
{
uint8_t x_96; uint8_t x_97; 
x_96 = 1;
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_96);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_93);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_96);
x_97 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_92);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_40);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_97);
return x_1;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; uint8_t x_104; 
x_98 = lean_ctor_get(x_40, 0);
x_99 = lean_ctor_get(x_40, 1);
x_100 = lean_ctor_get(x_40, 2);
x_101 = lean_ctor_get(x_40, 3);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_40);
x_102 = 1;
x_103 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_99);
lean_ctor_set(x_103, 2, x_100);
lean_ctor_set(x_103, 3, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*4, x_102);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_93);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_102);
x_104 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_92);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_103);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_104);
return x_1;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_105 = lean_ctor_get(x_38, 1);
x_106 = lean_ctor_get(x_38, 2);
x_107 = lean_ctor_get(x_38, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_38);
x_108 = lean_ctor_get(x_40, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_40, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_40, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_40, 3);
lean_inc(x_111);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_112 = x_40;
} else {
 lean_dec_ref(x_40);
 x_112 = lean_box(0);
}
x_113 = 1;
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(1, 4, 1);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_109);
lean_ctor_set(x_114, 2, x_110);
lean_ctor_set(x_114, 3, x_111);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_113);
x_115 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_34);
lean_ctor_set(x_115, 2, x_35);
lean_ctor_set(x_115, 3, x_36);
lean_ctor_set_uint8(x_115, sizeof(void*)*4, x_113);
x_116 = 0;
lean_ctor_set(x_1, 3, x_115);
lean_ctor_set(x_1, 2, x_106);
lean_ctor_set(x_1, 1, x_105);
lean_ctor_set(x_1, 0, x_114);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_116);
return x_1;
}
}
else
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_38, 3);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
lean_free_object(x_1);
x_118 = !lean_is_exclusive(x_40);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_119 = lean_ctor_get(x_40, 3);
lean_dec(x_119);
x_120 = lean_ctor_get(x_40, 2);
lean_dec(x_120);
x_121 = lean_ctor_get(x_40, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_40, 0);
lean_dec(x_122);
x_123 = 1;
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_123);
return x_40;
}
else
{
uint8_t x_124; lean_object* x_125; 
lean_dec(x_40);
x_124 = 1;
x_125 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_125, 0, x_38);
lean_ctor_set(x_125, 1, x_34);
lean_ctor_set(x_125, 2, x_35);
lean_ctor_set(x_125, 3, x_36);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_124);
return x_125;
}
}
else
{
uint8_t x_126; 
x_126 = lean_ctor_get_uint8(x_117, sizeof(void*)*4);
if (x_126 == 0)
{
uint8_t x_127; 
lean_free_object(x_1);
x_127 = !lean_is_exclusive(x_38);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_38, 1);
x_129 = lean_ctor_get(x_38, 2);
x_130 = lean_ctor_get(x_38, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_38, 0);
lean_dec(x_131);
x_132 = !lean_is_exclusive(x_117);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; 
x_133 = lean_ctor_get(x_117, 0);
x_134 = lean_ctor_get(x_117, 1);
x_135 = lean_ctor_get(x_117, 2);
x_136 = lean_ctor_get(x_117, 3);
x_137 = 1;
lean_inc(x_40);
lean_ctor_set(x_117, 3, x_133);
lean_ctor_set(x_117, 2, x_129);
lean_ctor_set(x_117, 1, x_128);
lean_ctor_set(x_117, 0, x_40);
x_138 = !lean_is_exclusive(x_40);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_139 = lean_ctor_get(x_40, 3);
lean_dec(x_139);
x_140 = lean_ctor_get(x_40, 2);
lean_dec(x_140);
x_141 = lean_ctor_get(x_40, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_40, 0);
lean_dec(x_142);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_137);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 0, x_136);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_137);
x_143 = 0;
lean_ctor_set(x_38, 3, x_40);
lean_ctor_set(x_38, 2, x_135);
lean_ctor_set(x_38, 1, x_134);
lean_ctor_set(x_38, 0, x_117);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_143);
return x_38;
}
else
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_40);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_137);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_136);
lean_ctor_set(x_144, 1, x_34);
lean_ctor_set(x_144, 2, x_35);
lean_ctor_set(x_144, 3, x_36);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_137);
x_145 = 0;
lean_ctor_set(x_38, 3, x_144);
lean_ctor_set(x_38, 2, x_135);
lean_ctor_set(x_38, 1, x_134);
lean_ctor_set(x_38, 0, x_117);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_145);
return x_38;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_146 = lean_ctor_get(x_117, 0);
x_147 = lean_ctor_get(x_117, 1);
x_148 = lean_ctor_get(x_117, 2);
x_149 = lean_ctor_get(x_117, 3);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_117);
x_150 = 1;
lean_inc(x_40);
x_151 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_151, 0, x_40);
lean_ctor_set(x_151, 1, x_128);
lean_ctor_set(x_151, 2, x_129);
lean_ctor_set(x_151, 3, x_146);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_152 = x_40;
} else {
 lean_dec_ref(x_40);
 x_152 = lean_box(0);
}
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_150);
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 4, 1);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_34);
lean_ctor_set(x_153, 2, x_35);
lean_ctor_set(x_153, 3, x_36);
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_150);
x_154 = 0;
lean_ctor_set(x_38, 3, x_153);
lean_ctor_set(x_38, 2, x_148);
lean_ctor_set(x_38, 1, x_147);
lean_ctor_set(x_38, 0, x_151);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_154);
return x_38;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; 
x_155 = lean_ctor_get(x_38, 1);
x_156 = lean_ctor_get(x_38, 2);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_38);
x_157 = lean_ctor_get(x_117, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_117, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_117, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_117, 3);
lean_inc(x_160);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 x_161 = x_117;
} else {
 lean_dec_ref(x_117);
 x_161 = lean_box(0);
}
x_162 = 1;
lean_inc(x_40);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(1, 4, 1);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_40);
lean_ctor_set(x_163, 1, x_155);
lean_ctor_set(x_163, 2, x_156);
lean_ctor_set(x_163, 3, x_157);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_164 = x_40;
} else {
 lean_dec_ref(x_40);
 x_164 = lean_box(0);
}
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_162);
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 4, 1);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_160);
lean_ctor_set(x_165, 1, x_34);
lean_ctor_set(x_165, 2, x_35);
lean_ctor_set(x_165, 3, x_36);
lean_ctor_set_uint8(x_165, sizeof(void*)*4, x_162);
x_166 = 0;
x_167 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_167, 0, x_163);
lean_ctor_set(x_167, 1, x_158);
lean_ctor_set(x_167, 2, x_159);
lean_ctor_set(x_167, 3, x_165);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_166);
return x_167;
}
}
else
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_38);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_ctor_get(x_38, 3);
lean_dec(x_169);
x_170 = lean_ctor_get(x_38, 0);
lean_dec(x_170);
x_171 = !lean_is_exclusive(x_40);
if (x_171 == 0)
{
uint8_t x_172; 
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_126);
x_172 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_172);
return x_1;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_173 = lean_ctor_get(x_40, 0);
x_174 = lean_ctor_get(x_40, 1);
x_175 = lean_ctor_get(x_40, 2);
x_176 = lean_ctor_get(x_40, 3);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_40);
x_177 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_174);
lean_ctor_set(x_177, 2, x_175);
lean_ctor_set(x_177, 3, x_176);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_126);
lean_ctor_set(x_38, 0, x_177);
x_178 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_178);
return x_1;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_179 = lean_ctor_get(x_38, 1);
x_180 = lean_ctor_get(x_38, 2);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_38);
x_181 = lean_ctor_get(x_40, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_40, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_40, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_40, 3);
lean_inc(x_184);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_185 = x_40;
} else {
 lean_dec_ref(x_40);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 4, 1);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_181);
lean_ctor_set(x_186, 1, x_182);
lean_ctor_set(x_186, 2, x_183);
lean_ctor_set(x_186, 3, x_184);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_126);
x_187 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_179);
lean_ctor_set(x_187, 2, x_180);
lean_ctor_set(x_187, 3, x_117);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_39);
x_188 = 1;
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_189; 
x_189 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
case 1:
{
uint8_t x_190; 
lean_dec(x_35);
lean_dec(x_34);
x_190 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_190);
return x_1;
}
default: 
{
lean_object* x_191; uint8_t x_192; 
x_191 = l_Lean_RBNode_ins___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__6(x_36, x_2, x_3);
x_192 = lean_ctor_get_uint8(x_191, sizeof(void*)*4);
if (x_192 == 0)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_191, 3);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_191);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_196 = lean_ctor_get(x_191, 3);
lean_dec(x_196);
x_197 = lean_ctor_get(x_191, 0);
lean_dec(x_197);
lean_ctor_set(x_191, 0, x_194);
x_198 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_198);
return x_1;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_199 = lean_ctor_get(x_191, 1);
x_200 = lean_ctor_get(x_191, 2);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_191);
x_201 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_201, 0, x_194);
lean_ctor_set(x_201, 1, x_199);
lean_ctor_set(x_201, 2, x_200);
lean_ctor_set(x_201, 3, x_194);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_192);
x_202 = 1;
lean_ctor_set(x_1, 3, x_201);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
}
}
else
{
uint8_t x_203; 
x_203 = lean_ctor_get_uint8(x_194, sizeof(void*)*4);
if (x_203 == 0)
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_191);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_191, 1);
x_206 = lean_ctor_get(x_191, 2);
x_207 = lean_ctor_get(x_191, 3);
lean_dec(x_207);
x_208 = lean_ctor_get(x_191, 0);
lean_dec(x_208);
x_209 = !lean_is_exclusive(x_194);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; 
x_210 = lean_ctor_get(x_194, 0);
x_211 = lean_ctor_get(x_194, 1);
x_212 = lean_ctor_get(x_194, 2);
x_213 = lean_ctor_get(x_194, 3);
x_214 = 1;
lean_ctor_set(x_194, 3, x_193);
lean_ctor_set(x_194, 2, x_35);
lean_ctor_set(x_194, 1, x_34);
lean_ctor_set(x_194, 0, x_33);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_214);
lean_ctor_set(x_191, 3, x_213);
lean_ctor_set(x_191, 2, x_212);
lean_ctor_set(x_191, 1, x_211);
lean_ctor_set(x_191, 0, x_210);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_214);
x_215 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_215);
return x_1;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; uint8_t x_222; 
x_216 = lean_ctor_get(x_194, 0);
x_217 = lean_ctor_get(x_194, 1);
x_218 = lean_ctor_get(x_194, 2);
x_219 = lean_ctor_get(x_194, 3);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_194);
x_220 = 1;
x_221 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_221, 0, x_33);
lean_ctor_set(x_221, 1, x_34);
lean_ctor_set(x_221, 2, x_35);
lean_ctor_set(x_221, 3, x_193);
lean_ctor_set_uint8(x_221, sizeof(void*)*4, x_220);
lean_ctor_set(x_191, 3, x_219);
lean_ctor_set(x_191, 2, x_218);
lean_ctor_set(x_191, 1, x_217);
lean_ctor_set(x_191, 0, x_216);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_220);
x_222 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_221);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_222);
return x_1;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_223 = lean_ctor_get(x_191, 1);
x_224 = lean_ctor_get(x_191, 2);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_191);
x_225 = lean_ctor_get(x_194, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_194, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_194, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_194, 3);
lean_inc(x_228);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_229 = x_194;
} else {
 lean_dec_ref(x_194);
 x_229 = lean_box(0);
}
x_230 = 1;
if (lean_is_scalar(x_229)) {
 x_231 = lean_alloc_ctor(1, 4, 1);
} else {
 x_231 = x_229;
}
lean_ctor_set(x_231, 0, x_33);
lean_ctor_set(x_231, 1, x_34);
lean_ctor_set(x_231, 2, x_35);
lean_ctor_set(x_231, 3, x_193);
lean_ctor_set_uint8(x_231, sizeof(void*)*4, x_230);
x_232 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_232, 0, x_225);
lean_ctor_set(x_232, 1, x_226);
lean_ctor_set(x_232, 2, x_227);
lean_ctor_set(x_232, 3, x_228);
lean_ctor_set_uint8(x_232, sizeof(void*)*4, x_230);
x_233 = 0;
lean_ctor_set(x_1, 3, x_232);
lean_ctor_set(x_1, 2, x_224);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_1, 0, x_231);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
}
else
{
uint8_t x_234; 
lean_free_object(x_1);
x_234 = !lean_is_exclusive(x_194);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_235 = lean_ctor_get(x_194, 3);
lean_dec(x_235);
x_236 = lean_ctor_get(x_194, 2);
lean_dec(x_236);
x_237 = lean_ctor_get(x_194, 1);
lean_dec(x_237);
x_238 = lean_ctor_get(x_194, 0);
lean_dec(x_238);
x_239 = 1;
lean_ctor_set(x_194, 3, x_191);
lean_ctor_set(x_194, 2, x_35);
lean_ctor_set(x_194, 1, x_34);
lean_ctor_set(x_194, 0, x_33);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_239);
return x_194;
}
else
{
uint8_t x_240; lean_object* x_241; 
lean_dec(x_194);
x_240 = 1;
x_241 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_241, 0, x_33);
lean_ctor_set(x_241, 1, x_34);
lean_ctor_set(x_241, 2, x_35);
lean_ctor_set(x_241, 3, x_191);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_240);
return x_241;
}
}
}
}
else
{
uint8_t x_242; 
x_242 = lean_ctor_get_uint8(x_193, sizeof(void*)*4);
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = !lean_is_exclusive(x_191);
if (x_243 == 0)
{
lean_object* x_244; uint8_t x_245; 
x_244 = lean_ctor_get(x_191, 0);
lean_dec(x_244);
x_245 = !lean_is_exclusive(x_193);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_251; 
x_246 = lean_ctor_get(x_193, 0);
x_247 = lean_ctor_get(x_193, 1);
x_248 = lean_ctor_get(x_193, 2);
x_249 = lean_ctor_get(x_193, 3);
x_250 = 1;
lean_ctor_set(x_193, 3, x_246);
lean_ctor_set(x_193, 2, x_35);
lean_ctor_set(x_193, 1, x_34);
lean_ctor_set(x_193, 0, x_33);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_250);
lean_ctor_set(x_191, 0, x_249);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_250);
x_251 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_248);
lean_ctor_set(x_1, 1, x_247);
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_251);
return x_1;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; uint8_t x_258; 
x_252 = lean_ctor_get(x_193, 0);
x_253 = lean_ctor_get(x_193, 1);
x_254 = lean_ctor_get(x_193, 2);
x_255 = lean_ctor_get(x_193, 3);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_193);
x_256 = 1;
x_257 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_257, 0, x_33);
lean_ctor_set(x_257, 1, x_34);
lean_ctor_set(x_257, 2, x_35);
lean_ctor_set(x_257, 3, x_252);
lean_ctor_set_uint8(x_257, sizeof(void*)*4, x_256);
lean_ctor_set(x_191, 0, x_255);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_256);
x_258 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_254);
lean_ctor_set(x_1, 1, x_253);
lean_ctor_set(x_1, 0, x_257);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_258);
return x_1;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_259 = lean_ctor_get(x_191, 1);
x_260 = lean_ctor_get(x_191, 2);
x_261 = lean_ctor_get(x_191, 3);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_191);
x_262 = lean_ctor_get(x_193, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_193, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_193, 2);
lean_inc(x_264);
x_265 = lean_ctor_get(x_193, 3);
lean_inc(x_265);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_266 = x_193;
} else {
 lean_dec_ref(x_193);
 x_266 = lean_box(0);
}
x_267 = 1;
if (lean_is_scalar(x_266)) {
 x_268 = lean_alloc_ctor(1, 4, 1);
} else {
 x_268 = x_266;
}
lean_ctor_set(x_268, 0, x_33);
lean_ctor_set(x_268, 1, x_34);
lean_ctor_set(x_268, 2, x_35);
lean_ctor_set(x_268, 3, x_262);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_267);
x_269 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_269, 0, x_265);
lean_ctor_set(x_269, 1, x_259);
lean_ctor_set(x_269, 2, x_260);
lean_ctor_set(x_269, 3, x_261);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_267);
x_270 = 0;
lean_ctor_set(x_1, 3, x_269);
lean_ctor_set(x_1, 2, x_264);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_268);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
return x_1;
}
}
else
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_191, 3);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
lean_free_object(x_1);
x_272 = !lean_is_exclusive(x_193);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_273 = lean_ctor_get(x_193, 3);
lean_dec(x_273);
x_274 = lean_ctor_get(x_193, 2);
lean_dec(x_274);
x_275 = lean_ctor_get(x_193, 1);
lean_dec(x_275);
x_276 = lean_ctor_get(x_193, 0);
lean_dec(x_276);
x_277 = 1;
lean_ctor_set(x_193, 3, x_191);
lean_ctor_set(x_193, 2, x_35);
lean_ctor_set(x_193, 1, x_34);
lean_ctor_set(x_193, 0, x_33);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_277);
return x_193;
}
else
{
uint8_t x_278; lean_object* x_279; 
lean_dec(x_193);
x_278 = 1;
x_279 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_279, 0, x_33);
lean_ctor_set(x_279, 1, x_34);
lean_ctor_set(x_279, 2, x_35);
lean_ctor_set(x_279, 3, x_191);
lean_ctor_set_uint8(x_279, sizeof(void*)*4, x_278);
return x_279;
}
}
else
{
uint8_t x_280; 
x_280 = lean_ctor_get_uint8(x_271, sizeof(void*)*4);
if (x_280 == 0)
{
uint8_t x_281; 
lean_free_object(x_1);
x_281 = !lean_is_exclusive(x_191);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_282 = lean_ctor_get(x_191, 3);
lean_dec(x_282);
x_283 = lean_ctor_get(x_191, 0);
lean_dec(x_283);
x_284 = !lean_is_exclusive(x_271);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_290; 
x_285 = lean_ctor_get(x_271, 0);
x_286 = lean_ctor_get(x_271, 1);
x_287 = lean_ctor_get(x_271, 2);
x_288 = lean_ctor_get(x_271, 3);
x_289 = 1;
lean_inc(x_193);
lean_ctor_set(x_271, 3, x_193);
lean_ctor_set(x_271, 2, x_35);
lean_ctor_set(x_271, 1, x_34);
lean_ctor_set(x_271, 0, x_33);
x_290 = !lean_is_exclusive(x_193);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_291 = lean_ctor_get(x_193, 3);
lean_dec(x_291);
x_292 = lean_ctor_get(x_193, 2);
lean_dec(x_292);
x_293 = lean_ctor_get(x_193, 1);
lean_dec(x_293);
x_294 = lean_ctor_get(x_193, 0);
lean_dec(x_294);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_289);
lean_ctor_set(x_193, 3, x_288);
lean_ctor_set(x_193, 2, x_287);
lean_ctor_set(x_193, 1, x_286);
lean_ctor_set(x_193, 0, x_285);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_289);
x_295 = 0;
lean_ctor_set(x_191, 3, x_193);
lean_ctor_set(x_191, 0, x_271);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_295);
return x_191;
}
else
{
lean_object* x_296; uint8_t x_297; 
lean_dec(x_193);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_289);
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_285);
lean_ctor_set(x_296, 1, x_286);
lean_ctor_set(x_296, 2, x_287);
lean_ctor_set(x_296, 3, x_288);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_289);
x_297 = 0;
lean_ctor_set(x_191, 3, x_296);
lean_ctor_set(x_191, 0, x_271);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_297);
return x_191;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_298 = lean_ctor_get(x_271, 0);
x_299 = lean_ctor_get(x_271, 1);
x_300 = lean_ctor_get(x_271, 2);
x_301 = lean_ctor_get(x_271, 3);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_271);
x_302 = 1;
lean_inc(x_193);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_33);
lean_ctor_set(x_303, 1, x_34);
lean_ctor_set(x_303, 2, x_35);
lean_ctor_set(x_303, 3, x_193);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_304 = x_193;
} else {
 lean_dec_ref(x_193);
 x_304 = lean_box(0);
}
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_302);
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 4, 1);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_298);
lean_ctor_set(x_305, 1, x_299);
lean_ctor_set(x_305, 2, x_300);
lean_ctor_set(x_305, 3, x_301);
lean_ctor_set_uint8(x_305, sizeof(void*)*4, x_302);
x_306 = 0;
lean_ctor_set(x_191, 3, x_305);
lean_ctor_set(x_191, 0, x_303);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_306);
return x_191;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; 
x_307 = lean_ctor_get(x_191, 1);
x_308 = lean_ctor_get(x_191, 2);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_191);
x_309 = lean_ctor_get(x_271, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_271, 1);
lean_inc(x_310);
x_311 = lean_ctor_get(x_271, 2);
lean_inc(x_311);
x_312 = lean_ctor_get(x_271, 3);
lean_inc(x_312);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 lean_ctor_release(x_271, 3);
 x_313 = x_271;
} else {
 lean_dec_ref(x_271);
 x_313 = lean_box(0);
}
x_314 = 1;
lean_inc(x_193);
if (lean_is_scalar(x_313)) {
 x_315 = lean_alloc_ctor(1, 4, 1);
} else {
 x_315 = x_313;
}
lean_ctor_set(x_315, 0, x_33);
lean_ctor_set(x_315, 1, x_34);
lean_ctor_set(x_315, 2, x_35);
lean_ctor_set(x_315, 3, x_193);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_316 = x_193;
} else {
 lean_dec_ref(x_193);
 x_316 = lean_box(0);
}
lean_ctor_set_uint8(x_315, sizeof(void*)*4, x_314);
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 4, 1);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_310);
lean_ctor_set(x_317, 2, x_311);
lean_ctor_set(x_317, 3, x_312);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_314);
x_318 = 0;
x_319 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_319, 0, x_315);
lean_ctor_set(x_319, 1, x_307);
lean_ctor_set(x_319, 2, x_308);
lean_ctor_set(x_319, 3, x_317);
lean_ctor_set_uint8(x_319, sizeof(void*)*4, x_318);
return x_319;
}
}
else
{
uint8_t x_320; 
x_320 = !lean_is_exclusive(x_191);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_321 = lean_ctor_get(x_191, 3);
lean_dec(x_321);
x_322 = lean_ctor_get(x_191, 0);
lean_dec(x_322);
x_323 = !lean_is_exclusive(x_193);
if (x_323 == 0)
{
uint8_t x_324; 
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_280);
x_324 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_324);
return x_1;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_325 = lean_ctor_get(x_193, 0);
x_326 = lean_ctor_get(x_193, 1);
x_327 = lean_ctor_get(x_193, 2);
x_328 = lean_ctor_get(x_193, 3);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_193);
x_329 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_329, 0, x_325);
lean_ctor_set(x_329, 1, x_326);
lean_ctor_set(x_329, 2, x_327);
lean_ctor_set(x_329, 3, x_328);
lean_ctor_set_uint8(x_329, sizeof(void*)*4, x_280);
lean_ctor_set(x_191, 0, x_329);
x_330 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_330);
return x_1;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_331 = lean_ctor_get(x_191, 1);
x_332 = lean_ctor_get(x_191, 2);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_191);
x_333 = lean_ctor_get(x_193, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_193, 1);
lean_inc(x_334);
x_335 = lean_ctor_get(x_193, 2);
lean_inc(x_335);
x_336 = lean_ctor_get(x_193, 3);
lean_inc(x_336);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_337 = x_193;
} else {
 lean_dec_ref(x_193);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_334);
lean_ctor_set(x_338, 2, x_335);
lean_ctor_set(x_338, 3, x_336);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_280);
x_339 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_331);
lean_ctor_set(x_339, 2, x_332);
lean_ctor_set(x_339, 3, x_271);
lean_ctor_set_uint8(x_339, sizeof(void*)*4, x_192);
x_340 = 1;
lean_ctor_set(x_1, 3, x_339);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_340);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_341; 
x_341 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_341);
return x_1;
}
}
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_342 = lean_ctor_get(x_1, 0);
x_343 = lean_ctor_get(x_1, 1);
x_344 = lean_ctor_get(x_1, 2);
x_345 = lean_ctor_get(x_1, 3);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_1);
x_346 = l_Lean_Name_quickCmp(x_2, x_343);
switch (x_346) {
case 0:
{
lean_object* x_347; uint8_t x_348; 
x_347 = l_Lean_RBNode_ins___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__6(x_342, x_2, x_3);
x_348 = lean_ctor_get_uint8(x_347, sizeof(void*)*4);
if (x_348 == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_347, 0);
lean_inc(x_349);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; 
x_350 = lean_ctor_get(x_347, 3);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; 
x_351 = lean_ctor_get(x_347, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_347, 2);
lean_inc(x_352);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_353 = x_347;
} else {
 lean_dec_ref(x_347);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 4, 1);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_350);
lean_ctor_set(x_354, 1, x_351);
lean_ctor_set(x_354, 2, x_352);
lean_ctor_set(x_354, 3, x_350);
lean_ctor_set_uint8(x_354, sizeof(void*)*4, x_348);
x_355 = 1;
x_356 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_343);
lean_ctor_set(x_356, 2, x_344);
lean_ctor_set(x_356, 3, x_345);
lean_ctor_set_uint8(x_356, sizeof(void*)*4, x_355);
return x_356;
}
else
{
uint8_t x_357; 
x_357 = lean_ctor_get_uint8(x_350, sizeof(void*)*4);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_358 = lean_ctor_get(x_347, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_347, 2);
lean_inc(x_359);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_360 = x_347;
} else {
 lean_dec_ref(x_347);
 x_360 = lean_box(0);
}
x_361 = lean_ctor_get(x_350, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_350, 1);
lean_inc(x_362);
x_363 = lean_ctor_get(x_350, 2);
lean_inc(x_363);
x_364 = lean_ctor_get(x_350, 3);
lean_inc(x_364);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_365 = x_350;
} else {
 lean_dec_ref(x_350);
 x_365 = lean_box(0);
}
x_366 = 1;
if (lean_is_scalar(x_365)) {
 x_367 = lean_alloc_ctor(1, 4, 1);
} else {
 x_367 = x_365;
}
lean_ctor_set(x_367, 0, x_349);
lean_ctor_set(x_367, 1, x_358);
lean_ctor_set(x_367, 2, x_359);
lean_ctor_set(x_367, 3, x_361);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_366);
if (lean_is_scalar(x_360)) {
 x_368 = lean_alloc_ctor(1, 4, 1);
} else {
 x_368 = x_360;
}
lean_ctor_set(x_368, 0, x_364);
lean_ctor_set(x_368, 1, x_343);
lean_ctor_set(x_368, 2, x_344);
lean_ctor_set(x_368, 3, x_345);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_366);
x_369 = 0;
x_370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_362);
lean_ctor_set(x_370, 2, x_363);
lean_ctor_set(x_370, 3, x_368);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_369);
return x_370;
}
else
{
lean_object* x_371; uint8_t x_372; lean_object* x_373; 
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_371 = x_350;
} else {
 lean_dec_ref(x_350);
 x_371 = lean_box(0);
}
x_372 = 1;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_347);
lean_ctor_set(x_373, 1, x_343);
lean_ctor_set(x_373, 2, x_344);
lean_ctor_set(x_373, 3, x_345);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
return x_373;
}
}
}
else
{
uint8_t x_374; 
x_374 = lean_ctor_get_uint8(x_349, sizeof(void*)*4);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; 
x_375 = lean_ctor_get(x_347, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_347, 2);
lean_inc(x_376);
x_377 = lean_ctor_get(x_347, 3);
lean_inc(x_377);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_378 = x_347;
} else {
 lean_dec_ref(x_347);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_349, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_349, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_349, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_349, 3);
lean_inc(x_382);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_383 = x_349;
} else {
 lean_dec_ref(x_349);
 x_383 = lean_box(0);
}
x_384 = 1;
if (lean_is_scalar(x_383)) {
 x_385 = lean_alloc_ctor(1, 4, 1);
} else {
 x_385 = x_383;
}
lean_ctor_set(x_385, 0, x_379);
lean_ctor_set(x_385, 1, x_380);
lean_ctor_set(x_385, 2, x_381);
lean_ctor_set(x_385, 3, x_382);
lean_ctor_set_uint8(x_385, sizeof(void*)*4, x_384);
if (lean_is_scalar(x_378)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_378;
}
lean_ctor_set(x_386, 0, x_377);
lean_ctor_set(x_386, 1, x_343);
lean_ctor_set(x_386, 2, x_344);
lean_ctor_set(x_386, 3, x_345);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_384);
x_387 = 0;
x_388 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_375);
lean_ctor_set(x_388, 2, x_376);
lean_ctor_set(x_388, 3, x_386);
lean_ctor_set_uint8(x_388, sizeof(void*)*4, x_387);
return x_388;
}
else
{
lean_object* x_389; 
x_389 = lean_ctor_get(x_347, 3);
lean_inc(x_389);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; uint8_t x_391; lean_object* x_392; 
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_390 = x_349;
} else {
 lean_dec_ref(x_349);
 x_390 = lean_box(0);
}
x_391 = 1;
if (lean_is_scalar(x_390)) {
 x_392 = lean_alloc_ctor(1, 4, 1);
} else {
 x_392 = x_390;
}
lean_ctor_set(x_392, 0, x_347);
lean_ctor_set(x_392, 1, x_343);
lean_ctor_set(x_392, 2, x_344);
lean_ctor_set(x_392, 3, x_345);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_391);
return x_392;
}
else
{
uint8_t x_393; 
x_393 = lean_ctor_get_uint8(x_389, sizeof(void*)*4);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; 
x_394 = lean_ctor_get(x_347, 1);
lean_inc(x_394);
x_395 = lean_ctor_get(x_347, 2);
lean_inc(x_395);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_396 = x_347;
} else {
 lean_dec_ref(x_347);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_389, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_389, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_389, 2);
lean_inc(x_399);
x_400 = lean_ctor_get(x_389, 3);
lean_inc(x_400);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 lean_ctor_release(x_389, 2);
 lean_ctor_release(x_389, 3);
 x_401 = x_389;
} else {
 lean_dec_ref(x_389);
 x_401 = lean_box(0);
}
x_402 = 1;
lean_inc(x_349);
if (lean_is_scalar(x_401)) {
 x_403 = lean_alloc_ctor(1, 4, 1);
} else {
 x_403 = x_401;
}
lean_ctor_set(x_403, 0, x_349);
lean_ctor_set(x_403, 1, x_394);
lean_ctor_set(x_403, 2, x_395);
lean_ctor_set(x_403, 3, x_397);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_404 = x_349;
} else {
 lean_dec_ref(x_349);
 x_404 = lean_box(0);
}
lean_ctor_set_uint8(x_403, sizeof(void*)*4, x_402);
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(1, 4, 1);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_400);
lean_ctor_set(x_405, 1, x_343);
lean_ctor_set(x_405, 2, x_344);
lean_ctor_set(x_405, 3, x_345);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_402);
x_406 = 0;
if (lean_is_scalar(x_396)) {
 x_407 = lean_alloc_ctor(1, 4, 1);
} else {
 x_407 = x_396;
}
lean_ctor_set(x_407, 0, x_403);
lean_ctor_set(x_407, 1, x_398);
lean_ctor_set(x_407, 2, x_399);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
return x_407;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; 
x_408 = lean_ctor_get(x_347, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_347, 2);
lean_inc(x_409);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_410 = x_347;
} else {
 lean_dec_ref(x_347);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_349, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_349, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_349, 2);
lean_inc(x_413);
x_414 = lean_ctor_get(x_349, 3);
lean_inc(x_414);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_415 = x_349;
} else {
 lean_dec_ref(x_349);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(1, 4, 1);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_411);
lean_ctor_set(x_416, 1, x_412);
lean_ctor_set(x_416, 2, x_413);
lean_ctor_set(x_416, 3, x_414);
lean_ctor_set_uint8(x_416, sizeof(void*)*4, x_393);
if (lean_is_scalar(x_410)) {
 x_417 = lean_alloc_ctor(1, 4, 1);
} else {
 x_417 = x_410;
}
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_408);
lean_ctor_set(x_417, 2, x_409);
lean_ctor_set(x_417, 3, x_389);
lean_ctor_set_uint8(x_417, sizeof(void*)*4, x_348);
x_418 = 1;
x_419 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_343);
lean_ctor_set(x_419, 2, x_344);
lean_ctor_set(x_419, 3, x_345);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
return x_419;
}
}
}
}
}
else
{
uint8_t x_420; lean_object* x_421; 
x_420 = 1;
x_421 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_421, 0, x_347);
lean_ctor_set(x_421, 1, x_343);
lean_ctor_set(x_421, 2, x_344);
lean_ctor_set(x_421, 3, x_345);
lean_ctor_set_uint8(x_421, sizeof(void*)*4, x_420);
return x_421;
}
}
case 1:
{
uint8_t x_422; lean_object* x_423; 
lean_dec(x_344);
lean_dec(x_343);
x_422 = 1;
x_423 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_423, 0, x_342);
lean_ctor_set(x_423, 1, x_2);
lean_ctor_set(x_423, 2, x_3);
lean_ctor_set(x_423, 3, x_345);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
return x_423;
}
default: 
{
lean_object* x_424; uint8_t x_425; 
x_424 = l_Lean_RBNode_ins___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__6(x_345, x_2, x_3);
x_425 = lean_ctor_get_uint8(x_424, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; 
x_426 = lean_ctor_get(x_424, 0);
lean_inc(x_426);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; 
x_427 = lean_ctor_get(x_424, 3);
lean_inc(x_427);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; 
x_428 = lean_ctor_get(x_424, 1);
lean_inc(x_428);
x_429 = lean_ctor_get(x_424, 2);
lean_inc(x_429);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_430 = x_424;
} else {
 lean_dec_ref(x_424);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 4, 1);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_427);
lean_ctor_set(x_431, 1, x_428);
lean_ctor_set(x_431, 2, x_429);
lean_ctor_set(x_431, 3, x_427);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_425);
x_432 = 1;
x_433 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_433, 0, x_342);
lean_ctor_set(x_433, 1, x_343);
lean_ctor_set(x_433, 2, x_344);
lean_ctor_set(x_433, 3, x_431);
lean_ctor_set_uint8(x_433, sizeof(void*)*4, x_432);
return x_433;
}
else
{
uint8_t x_434; 
x_434 = lean_ctor_get_uint8(x_427, sizeof(void*)*4);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; 
x_435 = lean_ctor_get(x_424, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_424, 2);
lean_inc(x_436);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_437 = x_424;
} else {
 lean_dec_ref(x_424);
 x_437 = lean_box(0);
}
x_438 = lean_ctor_get(x_427, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_427, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_427, 2);
lean_inc(x_440);
x_441 = lean_ctor_get(x_427, 3);
lean_inc(x_441);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_442 = x_427;
} else {
 lean_dec_ref(x_427);
 x_442 = lean_box(0);
}
x_443 = 1;
if (lean_is_scalar(x_442)) {
 x_444 = lean_alloc_ctor(1, 4, 1);
} else {
 x_444 = x_442;
}
lean_ctor_set(x_444, 0, x_342);
lean_ctor_set(x_444, 1, x_343);
lean_ctor_set(x_444, 2, x_344);
lean_ctor_set(x_444, 3, x_426);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_443);
if (lean_is_scalar(x_437)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_437;
}
lean_ctor_set(x_445, 0, x_438);
lean_ctor_set(x_445, 1, x_439);
lean_ctor_set(x_445, 2, x_440);
lean_ctor_set(x_445, 3, x_441);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_443);
x_446 = 0;
x_447 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_447, 0, x_444);
lean_ctor_set(x_447, 1, x_435);
lean_ctor_set(x_447, 2, x_436);
lean_ctor_set(x_447, 3, x_445);
lean_ctor_set_uint8(x_447, sizeof(void*)*4, x_446);
return x_447;
}
else
{
lean_object* x_448; uint8_t x_449; lean_object* x_450; 
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_448 = x_427;
} else {
 lean_dec_ref(x_427);
 x_448 = lean_box(0);
}
x_449 = 1;
if (lean_is_scalar(x_448)) {
 x_450 = lean_alloc_ctor(1, 4, 1);
} else {
 x_450 = x_448;
}
lean_ctor_set(x_450, 0, x_342);
lean_ctor_set(x_450, 1, x_343);
lean_ctor_set(x_450, 2, x_344);
lean_ctor_set(x_450, 3, x_424);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
return x_450;
}
}
}
else
{
uint8_t x_451; 
x_451 = lean_ctor_get_uint8(x_426, sizeof(void*)*4);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; lean_object* x_465; 
x_452 = lean_ctor_get(x_424, 1);
lean_inc(x_452);
x_453 = lean_ctor_get(x_424, 2);
lean_inc(x_453);
x_454 = lean_ctor_get(x_424, 3);
lean_inc(x_454);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_455 = x_424;
} else {
 lean_dec_ref(x_424);
 x_455 = lean_box(0);
}
x_456 = lean_ctor_get(x_426, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_426, 1);
lean_inc(x_457);
x_458 = lean_ctor_get(x_426, 2);
lean_inc(x_458);
x_459 = lean_ctor_get(x_426, 3);
lean_inc(x_459);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_460 = x_426;
} else {
 lean_dec_ref(x_426);
 x_460 = lean_box(0);
}
x_461 = 1;
if (lean_is_scalar(x_460)) {
 x_462 = lean_alloc_ctor(1, 4, 1);
} else {
 x_462 = x_460;
}
lean_ctor_set(x_462, 0, x_342);
lean_ctor_set(x_462, 1, x_343);
lean_ctor_set(x_462, 2, x_344);
lean_ctor_set(x_462, 3, x_456);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
if (lean_is_scalar(x_455)) {
 x_463 = lean_alloc_ctor(1, 4, 1);
} else {
 x_463 = x_455;
}
lean_ctor_set(x_463, 0, x_459);
lean_ctor_set(x_463, 1, x_452);
lean_ctor_set(x_463, 2, x_453);
lean_ctor_set(x_463, 3, x_454);
lean_ctor_set_uint8(x_463, sizeof(void*)*4, x_461);
x_464 = 0;
x_465 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_457);
lean_ctor_set(x_465, 2, x_458);
lean_ctor_set(x_465, 3, x_463);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_464);
return x_465;
}
else
{
lean_object* x_466; 
x_466 = lean_ctor_get(x_424, 3);
lean_inc(x_466);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; uint8_t x_468; lean_object* x_469; 
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_467 = x_426;
} else {
 lean_dec_ref(x_426);
 x_467 = lean_box(0);
}
x_468 = 1;
if (lean_is_scalar(x_467)) {
 x_469 = lean_alloc_ctor(1, 4, 1);
} else {
 x_469 = x_467;
}
lean_ctor_set(x_469, 0, x_342);
lean_ctor_set(x_469, 1, x_343);
lean_ctor_set(x_469, 2, x_344);
lean_ctor_set(x_469, 3, x_424);
lean_ctor_set_uint8(x_469, sizeof(void*)*4, x_468);
return x_469;
}
else
{
uint8_t x_470; 
x_470 = lean_ctor_get_uint8(x_466, sizeof(void*)*4);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; lean_object* x_484; 
x_471 = lean_ctor_get(x_424, 1);
lean_inc(x_471);
x_472 = lean_ctor_get(x_424, 2);
lean_inc(x_472);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_473 = x_424;
} else {
 lean_dec_ref(x_424);
 x_473 = lean_box(0);
}
x_474 = lean_ctor_get(x_466, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_466, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_466, 2);
lean_inc(x_476);
x_477 = lean_ctor_get(x_466, 3);
lean_inc(x_477);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 lean_ctor_release(x_466, 2);
 lean_ctor_release(x_466, 3);
 x_478 = x_466;
} else {
 lean_dec_ref(x_466);
 x_478 = lean_box(0);
}
x_479 = 1;
lean_inc(x_426);
if (lean_is_scalar(x_478)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_478;
}
lean_ctor_set(x_480, 0, x_342);
lean_ctor_set(x_480, 1, x_343);
lean_ctor_set(x_480, 2, x_344);
lean_ctor_set(x_480, 3, x_426);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_481 = x_426;
} else {
 lean_dec_ref(x_426);
 x_481 = lean_box(0);
}
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_479);
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(1, 4, 1);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_474);
lean_ctor_set(x_482, 1, x_475);
lean_ctor_set(x_482, 2, x_476);
lean_ctor_set(x_482, 3, x_477);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_479);
x_483 = 0;
if (lean_is_scalar(x_473)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_473;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_471);
lean_ctor_set(x_484, 2, x_472);
lean_ctor_set(x_484, 3, x_482);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_483);
return x_484;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; lean_object* x_496; 
x_485 = lean_ctor_get(x_424, 1);
lean_inc(x_485);
x_486 = lean_ctor_get(x_424, 2);
lean_inc(x_486);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_487 = x_424;
} else {
 lean_dec_ref(x_424);
 x_487 = lean_box(0);
}
x_488 = lean_ctor_get(x_426, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_426, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_426, 2);
lean_inc(x_490);
x_491 = lean_ctor_get(x_426, 3);
lean_inc(x_491);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_492 = x_426;
} else {
 lean_dec_ref(x_426);
 x_492 = lean_box(0);
}
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(1, 4, 1);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_488);
lean_ctor_set(x_493, 1, x_489);
lean_ctor_set(x_493, 2, x_490);
lean_ctor_set(x_493, 3, x_491);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_470);
if (lean_is_scalar(x_487)) {
 x_494 = lean_alloc_ctor(1, 4, 1);
} else {
 x_494 = x_487;
}
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_485);
lean_ctor_set(x_494, 2, x_486);
lean_ctor_set(x_494, 3, x_466);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_425);
x_495 = 1;
x_496 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_496, 0, x_342);
lean_ctor_set(x_496, 1, x_343);
lean_ctor_set(x_496, 2, x_344);
lean_ctor_set(x_496, 3, x_494);
lean_ctor_set_uint8(x_496, sizeof(void*)*4, x_495);
return x_496;
}
}
}
}
}
else
{
uint8_t x_497; lean_object* x_498; 
x_497 = 1;
x_498 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_498, 0, x_342);
lean_ctor_set(x_498, 1, x_343);
lean_ctor_set(x_498, 2, x_344);
lean_ctor_set(x_498, 3, x_424);
lean_ctor_set_uint8(x_498, sizeof(void*)*4, x_497);
return x_498;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__6(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__6(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__3;
x_3 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__4;
x_4 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__5;
x_5 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_2);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_19 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__6;
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
x_21 = lean_alloc_ctor(6, 2, 0);
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
x_28 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__6;
lean_inc(x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
x_30 = lean_alloc_ctor(6, 2, 0);
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
lean_inc(x_9);
lean_inc(x_5);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_9, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_5, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
x_21 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__1(x_18, x_20);
lean_dec(x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_free_object(x_16);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_get(x_9, x_19);
lean_dec(x_9);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_take(x_5, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_RBNode_erase___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__2(x_20, x_27);
lean_dec(x_20);
x_30 = lean_st_ref_set(x_5, x_29, x_28);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_33, 1, x_12);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_3);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_12);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
x_41 = lean_ctor_get(x_3, 0);
lean_inc(x_41);
x_42 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__1(x_39, x_41);
lean_dec(x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_41);
lean_dec(x_9);
lean_dec(x_5);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_12);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_st_ref_get(x_9, x_40);
lean_dec(x_9);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_st_ref_take(x_5, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_RBNode_erase___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__2(x_41, x_49);
lean_dec(x_41);
x_52 = lean_st_ref_set(x_5, x_51, x_50);
lean_dec(x_5);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_45);
lean_ctor_set(x_55, 1, x_12);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_3);
lean_ctor_set(x_56, 1, x_55);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_11);
if (x_58 == 0)
{
return x_11;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_11, 0);
x_60 = lean_ctor_get(x_11, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_11);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_x", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_jp", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("`Code.bind` failed, empty `cases` found", 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12;
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
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_11, 3);
lean_inc(x_18);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
lean_free_object(x_2);
x_20 = lean_box(0);
x_21 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_11, x_20, x_3, x_4, x_5, x_6, x_7, x_8);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Expr_getAppFn(x_18);
x_23 = l_Lean_Expr_isFVar(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_18);
lean_free_object(x_2);
x_24 = lean_box(0);
x_25 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_11, x_24, x_3, x_4, x_5, x_6, x_7, x_8);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_inc(x_22);
x_26 = l_Lean_Expr_fvarId_x21(x_22);
lean_inc(x_26);
x_27 = l_Lean_Compiler_LCNF_getBinderName(x_26, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Name_getPrefix(x_28);
lean_dec(x_28);
x_31 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2;
x_32 = lean_name_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_18);
lean_free_object(x_2);
x_33 = lean_box(0);
x_34 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_11, x_33, x_3, x_4, x_5, x_6, x_7, x_29);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_inc(x_26);
x_35 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(x_26, x_4, x_5, x_6, x_7, x_29);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_18);
lean_free_object(x_2);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_box(0);
x_39 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_11, x_38, x_3, x_4, x_5, x_6, x_7, x_37);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_9);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_18, x_42);
x_44 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
lean_inc(x_43);
x_45 = lean_mk_array(x_43, x_44);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_sub(x_43, x_46);
lean_dec(x_43);
x_48 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_18, x_45, x_47);
x_49 = l_Lean_Compiler_LCNF_eraseLetDecl(x_11, x_4, x_5, x_6, x_7, x_40);
lean_dec(x_11);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_st_ref_get(x_7, x_50);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_st_ref_get(x_3, x_52);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
x_57 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__1(x_55, x_26);
lean_dec(x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; lean_object* x_63; size_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_free_object(x_53);
x_58 = lean_ctor_get(x_41, 2);
lean_inc(x_58);
lean_dec(x_41);
x_59 = lean_array_get_size(x_48);
x_60 = l_Array_toSubarray___rarg(x_58, x_42, x_59);
x_61 = lean_ctor_get(x_60, 2);
lean_inc(x_61);
x_62 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
x_64 = lean_usize_of_nat(x_63);
lean_dec(x_63);
x_65 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6;
x_66 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__4(x_60, x_62, x_64, x_65, x_3, x_4, x_5, x_6, x_7, x_56);
lean_dec(x_60);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
lean_dec(x_68);
x_72 = l_Lean_mkAppN(x_22, x_70);
x_73 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_74 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_72, x_73, x_4, x_5, x_6, x_7, x_69);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_1, 0);
lean_inc(x_77);
lean_dec(x_1);
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
x_79 = l_Lean_Expr_fvar___override(x_78);
x_80 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9;
x_81 = lean_array_push(x_80, x_79);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 1, x_81);
lean_ctor_set(x_2, 0, x_77);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_2);
x_83 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
lean_inc(x_7);
x_84 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_71, x_82, x_83, x_4, x_5, x_6, x_7, x_76);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_st_ref_get(x_7, x_86);
lean_dec(x_7);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_st_ref_take(x_3, x_88);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_85);
x_92 = l_Lean_RBNode_insert___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__5(x_90, x_26, x_85);
x_93 = lean_st_ref_set(x_3, x_92, x_91);
lean_dec(x_3);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_93, 0);
lean_dec(x_95);
x_96 = lean_ctor_get(x_85, 0);
lean_inc(x_96);
lean_dec(x_85);
x_97 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_48);
lean_ctor_set(x_93, 0, x_97);
return x_93;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
lean_dec(x_93);
x_99 = lean_ctor_get(x_85, 0);
lean_inc(x_99);
lean_dec(x_85);
x_100 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_48);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
}
else
{
uint8_t x_102; 
lean_dec(x_48);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_3);
x_102 = !lean_is_exclusive(x_84);
if (x_102 == 0)
{
return x_84;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_84, 0);
x_104 = lean_ctor_get(x_84, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_84);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_71);
lean_dec(x_48);
lean_dec(x_26);
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_74);
if (x_106 == 0)
{
return x_74;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_74, 0);
x_108 = lean_ctor_get(x_74, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_74);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_41);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_110 = lean_ctor_get(x_57, 0);
lean_inc(x_110);
lean_dec(x_57);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec(x_110);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 1, x_48);
lean_ctor_set(x_2, 0, x_111);
lean_ctor_set(x_53, 0, x_2);
return x_53;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_53, 0);
x_113 = lean_ctor_get(x_53, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_53);
x_114 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__1(x_112, x_26);
lean_dec(x_112);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; size_t x_119; lean_object* x_120; size_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_115 = lean_ctor_get(x_41, 2);
lean_inc(x_115);
lean_dec(x_41);
x_116 = lean_array_get_size(x_48);
x_117 = l_Array_toSubarray___rarg(x_115, x_42, x_116);
x_118 = lean_ctor_get(x_117, 2);
lean_inc(x_118);
x_119 = lean_usize_of_nat(x_118);
lean_dec(x_118);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
x_121 = lean_usize_of_nat(x_120);
lean_dec(x_120);
x_122 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6;
x_123 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__4(x_117, x_119, x_121, x_122, x_3, x_4, x_5, x_6, x_7, x_113);
lean_dec(x_117);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
lean_dec(x_124);
x_128 = lean_ctor_get(x_125, 0);
lean_inc(x_128);
lean_dec(x_125);
x_129 = l_Lean_mkAppN(x_22, x_127);
x_130 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_131 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_129, x_130, x_4, x_5, x_6, x_7, x_126);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_1, 0);
lean_inc(x_134);
lean_dec(x_1);
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
x_136 = l_Lean_Expr_fvar___override(x_135);
x_137 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9;
x_138 = lean_array_push(x_137, x_136);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 1, x_138);
lean_ctor_set(x_2, 0, x_134);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_132);
lean_ctor_set(x_139, 1, x_2);
x_140 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
lean_inc(x_7);
x_141 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_128, x_139, x_140, x_4, x_5, x_6, x_7, x_133);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_st_ref_get(x_7, x_143);
lean_dec(x_7);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_st_ref_take(x_3, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
lean_inc(x_142);
x_149 = l_Lean_RBNode_insert___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__5(x_147, x_26, x_142);
x_150 = lean_st_ref_set(x_3, x_149, x_148);
lean_dec(x_3);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_152 = x_150;
} else {
 lean_dec_ref(x_150);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_142, 0);
lean_inc(x_153);
lean_dec(x_142);
x_154 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_48);
if (lean_is_scalar(x_152)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_152;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_151);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_48);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_3);
x_156 = lean_ctor_get(x_141, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_141, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_158 = x_141;
} else {
 lean_dec_ref(x_141);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_128);
lean_dec(x_48);
lean_dec(x_26);
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_160 = lean_ctor_get(x_131, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_131, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_162 = x_131;
} else {
 lean_dec_ref(x_131);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_41);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_164 = lean_ctor_get(x_114, 0);
lean_inc(x_164);
lean_dec(x_114);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
lean_dec(x_164);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 1, x_48);
lean_ctor_set(x_2, 0, x_165);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_2);
lean_ctor_set(x_166, 1, x_113);
return x_166;
}
}
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_18);
lean_free_object(x_2);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_27);
if (x_167 == 0)
{
return x_27;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_27, 0);
x_169 = lean_ctor_get(x_27, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_27);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_171 = lean_ctor_get(x_2, 0);
lean_inc(x_171);
lean_dec(x_2);
x_172 = lean_ctor_get(x_9, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
x_174 = lean_name_eq(x_173, x_172);
lean_dec(x_172);
lean_dec(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_box(0);
x_176 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_171, x_175, x_3, x_4, x_5, x_6, x_7, x_8);
return x_176;
}
else
{
lean_object* x_177; uint8_t x_178; 
x_177 = lean_ctor_get(x_171, 3);
lean_inc(x_177);
x_178 = l_Lean_Expr_isApp(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_177);
x_179 = lean_box(0);
x_180 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_171, x_179, x_3, x_4, x_5, x_6, x_7, x_8);
return x_180;
}
else
{
lean_object* x_181; uint8_t x_182; 
x_181 = l_Lean_Expr_getAppFn(x_177);
x_182 = l_Lean_Expr_isFVar(x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_181);
lean_dec(x_177);
x_183 = lean_box(0);
x_184 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_171, x_183, x_3, x_4, x_5, x_6, x_7, x_8);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_inc(x_181);
x_185 = l_Lean_Expr_fvarId_x21(x_181);
lean_inc(x_185);
x_186 = l_Lean_Compiler_LCNF_getBinderName(x_185, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = l_Lean_Name_getPrefix(x_187);
lean_dec(x_187);
x_190 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2;
x_191 = lean_name_eq(x_189, x_190);
lean_dec(x_189);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_185);
lean_dec(x_181);
lean_dec(x_177);
x_192 = lean_box(0);
x_193 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_171, x_192, x_3, x_4, x_5, x_6, x_7, x_188);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; 
lean_inc(x_185);
x_194 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(x_185, x_4, x_5, x_6, x_7, x_188);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_185);
lean_dec(x_181);
lean_dec(x_177);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_box(0);
x_198 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_171, x_197, x_3, x_4, x_5, x_6, x_7, x_196);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_9);
x_199 = lean_ctor_get(x_194, 1);
lean_inc(x_199);
lean_dec(x_194);
x_200 = lean_ctor_get(x_195, 0);
lean_inc(x_200);
lean_dec(x_195);
x_201 = lean_unsigned_to_nat(0u);
x_202 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_177, x_201);
x_203 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
lean_inc(x_202);
x_204 = lean_mk_array(x_202, x_203);
x_205 = lean_unsigned_to_nat(1u);
x_206 = lean_nat_sub(x_202, x_205);
lean_dec(x_202);
x_207 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_177, x_204, x_206);
x_208 = l_Lean_Compiler_LCNF_eraseLetDecl(x_171, x_4, x_5, x_6, x_7, x_199);
lean_dec(x_171);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec(x_208);
x_210 = lean_st_ref_get(x_7, x_209);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_212 = lean_st_ref_get(x_3, x_211);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_215 = x_212;
} else {
 lean_dec_ref(x_212);
 x_215 = lean_box(0);
}
x_216 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__1(x_213, x_185);
lean_dec(x_213);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; size_t x_221; lean_object* x_222; size_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_215);
x_217 = lean_ctor_get(x_200, 2);
lean_inc(x_217);
lean_dec(x_200);
x_218 = lean_array_get_size(x_207);
x_219 = l_Array_toSubarray___rarg(x_217, x_201, x_218);
x_220 = lean_ctor_get(x_219, 2);
lean_inc(x_220);
x_221 = lean_usize_of_nat(x_220);
lean_dec(x_220);
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
x_223 = lean_usize_of_nat(x_222);
lean_dec(x_222);
x_224 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6;
x_225 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__4(x_219, x_221, x_223, x_224, x_3, x_4, x_5, x_6, x_7, x_214);
lean_dec(x_219);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_225, 1);
lean_inc(x_228);
lean_dec(x_225);
x_229 = lean_ctor_get(x_226, 0);
lean_inc(x_229);
lean_dec(x_226);
x_230 = lean_ctor_get(x_227, 0);
lean_inc(x_230);
lean_dec(x_227);
x_231 = l_Lean_mkAppN(x_181, x_229);
x_232 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_233 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_231, x_232, x_4, x_5, x_6, x_7, x_228);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_ctor_get(x_1, 0);
lean_inc(x_236);
lean_dec(x_1);
x_237 = lean_ctor_get(x_234, 0);
lean_inc(x_237);
x_238 = l_Lean_Expr_fvar___override(x_237);
x_239 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9;
x_240 = lean_array_push(x_239, x_238);
x_241 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_241, 0, x_236);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_234);
lean_ctor_set(x_242, 1, x_241);
x_243 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
lean_inc(x_7);
x_244 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_230, x_242, x_243, x_4, x_5, x_6, x_7, x_235);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_st_ref_get(x_7, x_246);
lean_dec(x_7);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
lean_dec(x_247);
x_249 = lean_st_ref_take(x_3, x_248);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
lean_inc(x_245);
x_252 = l_Lean_RBNode_insert___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__5(x_250, x_185, x_245);
x_253 = lean_st_ref_set(x_3, x_252, x_251);
lean_dec(x_3);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_255 = x_253;
} else {
 lean_dec_ref(x_253);
 x_255 = lean_box(0);
}
x_256 = lean_ctor_get(x_245, 0);
lean_inc(x_256);
lean_dec(x_245);
x_257 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_207);
if (lean_is_scalar(x_255)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_255;
}
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_254);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_207);
lean_dec(x_185);
lean_dec(x_7);
lean_dec(x_3);
x_259 = lean_ctor_get(x_244, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_244, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_261 = x_244;
} else {
 lean_dec_ref(x_244);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_230);
lean_dec(x_207);
lean_dec(x_185);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_263 = lean_ctor_get(x_233, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_233, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_265 = x_233;
} else {
 lean_dec_ref(x_233);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_200);
lean_dec(x_185);
lean_dec(x_181);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_267 = lean_ctor_get(x_216, 0);
lean_inc(x_267);
lean_dec(x_216);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
lean_dec(x_267);
x_269 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_207);
if (lean_is_scalar(x_215)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_215;
}
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_214);
return x_270;
}
}
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_185);
lean_dec(x_181);
lean_dec(x_177);
lean_dec(x_171);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_271 = lean_ctor_get(x_186, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_186, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_273 = x_186;
} else {
 lean_dec_ref(x_186);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
}
}
}
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_2, 0);
lean_inc(x_275);
lean_dec(x_2);
x_276 = lean_box(0);
x_277 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__1(x_1, x_9, x_275, x_276, x_3, x_4, x_5, x_6, x_7, x_8);
return x_277;
}
}
case 1:
{
uint8_t x_278; 
x_278 = !lean_is_exclusive(x_2);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_2, 0);
x_280 = lean_ctor_get(x_2, 1);
x_281 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_280, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_281) == 0)
{
uint8_t x_282; 
x_282 = !lean_is_exclusive(x_281);
if (x_282 == 0)
{
lean_object* x_283; 
x_283 = lean_ctor_get(x_281, 0);
lean_ctor_set(x_2, 1, x_283);
lean_ctor_set(x_281, 0, x_2);
return x_281;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_281, 0);
x_285 = lean_ctor_get(x_281, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_281);
lean_ctor_set(x_2, 1, x_284);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_2);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
else
{
uint8_t x_287; 
lean_free_object(x_2);
lean_dec(x_279);
x_287 = !lean_is_exclusive(x_281);
if (x_287 == 0)
{
return x_281;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_281, 0);
x_289 = lean_ctor_get(x_281, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_281);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
return x_290;
}
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_2, 0);
x_292 = lean_ctor_get(x_2, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_2);
x_293 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_292, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_296 = x_293;
} else {
 lean_dec_ref(x_293);
 x_296 = lean_box(0);
}
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_291);
lean_ctor_set(x_297, 1, x_294);
if (lean_is_scalar(x_296)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_296;
}
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_295);
return x_298;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_291);
x_299 = lean_ctor_get(x_293, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_293, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_301 = x_293;
} else {
 lean_dec_ref(x_293);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_299);
lean_ctor_set(x_302, 1, x_300);
return x_302;
}
}
}
case 2:
{
uint8_t x_303; 
x_303 = !lean_is_exclusive(x_2);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_304 = lean_ctor_get(x_2, 0);
x_305 = lean_ctor_get(x_2, 1);
x_306 = lean_ctor_get(x_304, 4);
lean_inc(x_306);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_307 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_306, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = lean_ctor_get(x_304, 2);
lean_inc(x_310);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_308);
lean_inc(x_310);
x_311 = l_Lean_Compiler_LCNF_Code_inferParamType(x_310, x_308, x_4, x_5, x_6, x_7, x_309);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
x_314 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_304, x_312, x_310, x_308, x_4, x_5, x_6, x_7, x_313);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
x_317 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_305, x_3, x_4, x_5, x_6, x_7, x_316);
if (lean_obj_tag(x_317) == 0)
{
uint8_t x_318; 
x_318 = !lean_is_exclusive(x_317);
if (x_318 == 0)
{
lean_object* x_319; 
x_319 = lean_ctor_get(x_317, 0);
lean_ctor_set(x_2, 1, x_319);
lean_ctor_set(x_2, 0, x_315);
lean_ctor_set(x_317, 0, x_2);
return x_317;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_317, 0);
x_321 = lean_ctor_get(x_317, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_317);
lean_ctor_set(x_2, 1, x_320);
lean_ctor_set(x_2, 0, x_315);
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_2);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
else
{
uint8_t x_323; 
lean_dec(x_315);
lean_free_object(x_2);
x_323 = !lean_is_exclusive(x_317);
if (x_323 == 0)
{
return x_317;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_317, 0);
x_325 = lean_ctor_get(x_317, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_317);
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
return x_326;
}
}
}
else
{
uint8_t x_327; 
lean_dec(x_310);
lean_dec(x_308);
lean_free_object(x_2);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_327 = !lean_is_exclusive(x_311);
if (x_327 == 0)
{
return x_311;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_311, 0);
x_329 = lean_ctor_get(x_311, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_311);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
return x_330;
}
}
}
else
{
uint8_t x_331; 
lean_free_object(x_2);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_331 = !lean_is_exclusive(x_307);
if (x_331 == 0)
{
return x_307;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_307, 0);
x_333 = lean_ctor_get(x_307, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_307);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
return x_334;
}
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_335 = lean_ctor_get(x_2, 0);
x_336 = lean_ctor_get(x_2, 1);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_2);
x_337 = lean_ctor_get(x_335, 4);
lean_inc(x_337);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_338 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_337, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = lean_ctor_get(x_335, 2);
lean_inc(x_341);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_339);
lean_inc(x_341);
x_342 = l_Lean_Compiler_LCNF_Code_inferParamType(x_341, x_339, x_4, x_5, x_6, x_7, x_340);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_335, x_343, x_341, x_339, x_4, x_5, x_6, x_7, x_344);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
x_348 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_336, x_3, x_4, x_5, x_6, x_7, x_347);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_351 = x_348;
} else {
 lean_dec_ref(x_348);
 x_351 = lean_box(0);
}
x_352 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_352, 0, x_346);
lean_ctor_set(x_352, 1, x_349);
if (lean_is_scalar(x_351)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_351;
}
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_350);
return x_353;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_346);
x_354 = lean_ctor_get(x_348, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_348, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_356 = x_348;
} else {
 lean_dec_ref(x_348);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_354);
lean_ctor_set(x_357, 1, x_355);
return x_357;
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_341);
lean_dec(x_339);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_358 = lean_ctor_get(x_342, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_342, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_360 = x_342;
} else {
 lean_dec_ref(x_342);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_359);
return x_361;
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_362 = lean_ctor_get(x_338, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_338, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_364 = x_338;
} else {
 lean_dec_ref(x_338);
 x_364 = lean_box(0);
}
if (lean_is_scalar(x_364)) {
 x_365 = lean_alloc_ctor(1, 2, 0);
} else {
 x_365 = x_364;
}
lean_ctor_set(x_365, 0, x_362);
lean_ctor_set(x_365, 1, x_363);
return x_365;
}
}
}
case 4:
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; size_t x_371; size_t x_372; lean_object* x_373; 
x_366 = lean_ctor_get(x_2, 0);
lean_inc(x_366);
lean_dec(x_2);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 2);
lean_inc(x_368);
x_369 = lean_ctor_get(x_366, 3);
lean_inc(x_369);
lean_dec(x_366);
x_370 = lean_array_get_size(x_369);
x_371 = lean_usize_of_nat(x_370);
lean_dec(x_370);
x_372 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_373 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7(x_1, x_371, x_372, x_369, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; uint8_t x_376; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
x_376 = l_Array_isEmpty___rarg(x_374);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; 
x_377 = lean_box(0);
x_378 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___lambda__2(x_374, x_367, x_368, x_377, x_3, x_4, x_5, x_6, x_7, x_375);
lean_dec(x_3);
return x_378;
}
else
{
lean_object* x_379; lean_object* x_380; uint8_t x_381; 
lean_dec(x_374);
lean_dec(x_368);
lean_dec(x_367);
x_379 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__13;
x_380 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8(x_379, x_3, x_4, x_5, x_6, x_7, x_375);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_381 = !lean_is_exclusive(x_380);
if (x_381 == 0)
{
return x_380;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_380, 0);
x_383 = lean_ctor_get(x_380, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_380);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
else
{
uint8_t x_385; 
lean_dec(x_368);
lean_dec(x_367);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_385 = !lean_is_exclusive(x_373);
if (x_385 == 0)
{
return x_373;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_373, 0);
x_387 = lean_ctor_get(x_373, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_373);
x_388 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
return x_388;
}
}
}
case 5:
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_389 = lean_ctor_get(x_2, 0);
lean_inc(x_389);
lean_dec(x_2);
x_390 = lean_ctor_get(x_1, 0);
lean_inc(x_390);
lean_dec(x_1);
x_391 = l_Lean_Expr_fvar___override(x_389);
x_392 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9;
x_393 = lean_array_push(x_392, x_391);
x_394 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_394, 0, x_390);
lean_ctor_set(x_394, 1, x_393);
x_395 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_8);
return x_395;
}
default: 
{
lean_object* x_396; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_2);
lean_ctor_set(x_396, 1, x_8);
return x_396;
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
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__4(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__7(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
x_13 = lean_box(0);
x_14 = lean_st_ref_get(x_6, x_7);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_mk_ref(x_13, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_17);
lean_inc(x_1);
x_19 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(x_1, x_11, x_17, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_6, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_st_ref_get(x_17, x_23);
lean_dec(x_17);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_20);
x_27 = l_Lean_Compiler_LCNF_mkCasesResultType(x_20, x_3, x_4, x_5, x_6, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_27, 0);
lean_ctor_set(x_2, 3, x_20);
lean_ctor_set(x_2, 1, x_29);
x_30 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_30, 0, x_2);
x_31 = l_Lean_RBNode_fold___at_Lean_Compiler_LCNF_ToLCNF_bindCases___spec__1(x_30, x_25);
lean_dec(x_25);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
lean_ctor_set(x_2, 3, x_20);
lean_ctor_set(x_2, 1, x_33);
x_35 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_35, 0, x_2);
x_36 = l_Lean_RBNode_fold___at_Lean_Compiler_LCNF_ToLCNF_bindCases___spec__1(x_35, x_25);
lean_dec(x_25);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_25);
lean_dec(x_20);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_27);
if (x_39 == 0)
{
return x_27;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_27, 0);
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_27);
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
lean_dec(x_17);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_19, 0);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_47 = lean_ctor_get(x_2, 0);
x_48 = lean_ctor_get(x_2, 2);
x_49 = lean_ctor_get(x_2, 3);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_2);
x_50 = lean_box(0);
x_51 = lean_st_ref_get(x_6, x_7);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_st_mk_ref(x_50, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_54);
lean_inc(x_1);
x_56 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(x_1, x_49, x_54, x_3, x_4, x_5, x_6, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_st_ref_get(x_6, x_58);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_st_ref_get(x_54, x_60);
lean_dec(x_54);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_57);
x_64 = l_Lean_Compiler_LCNF_mkCasesResultType(x_57, x_3, x_4, x_5, x_6, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_47);
lean_ctor_set(x_68, 1, x_65);
lean_ctor_set(x_68, 2, x_48);
lean_ctor_set(x_68, 3, x_57);
x_69 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Lean_RBNode_fold___at_Lean_Compiler_LCNF_ToLCNF_bindCases___spec__1(x_69, x_62);
lean_dec(x_62);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_70);
if (lean_is_scalar(x_67)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_67;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_62);
lean_dec(x_57);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_1);
x_73 = lean_ctor_get(x_64, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_64, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_75 = x_64;
} else {
 lean_dec_ref(x_64);
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
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_77 = lean_ctor_get(x_56, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_56, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_79 = x_56;
} else {
 lean_dec_ref(x_56);
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
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__2;
x_3 = lean_unsigned_to_nat(77u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
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
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_100; uint8_t x_101; 
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_sub(x_2, x_66);
x_100 = lean_array_get_size(x_1);
x_101 = lean_nat_dec_lt(x_67, x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_103 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___spec__2(x_102);
switch (lean_obj_tag(x_103)) {
case 0:
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_2);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_3);
x_2 = x_67;
x_3 = x_105;
goto _start;
}
case 1:
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_2);
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
lean_dec(x_103);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_3);
x_2 = x_67;
x_3 = x_108;
goto _start;
}
case 2:
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_2);
x_110 = lean_ctor_get(x_103, 0);
lean_inc(x_110);
lean_dec(x_103);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_3);
x_2 = x_67;
x_3 = x_111;
goto _start;
}
case 3:
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_2);
x_113 = lean_ctor_get(x_103, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_103, 1);
lean_inc(x_114);
lean_dec(x_103);
x_68 = x_113;
x_69 = x_114;
goto block_99;
}
default: 
{
lean_object* x_115; 
lean_dec(x_103);
lean_dec(x_67);
x_115 = lean_box(0);
x_9 = x_115;
goto block_62;
}
}
}
else
{
lean_object* x_116; 
x_116 = lean_array_fget(x_1, x_67);
switch (lean_obj_tag(x_116)) {
case 0:
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_2);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_3);
x_2 = x_67;
x_3 = x_118;
goto _start;
}
case 1:
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_2);
x_120 = lean_ctor_get(x_116, 0);
lean_inc(x_120);
lean_dec(x_116);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_3);
x_2 = x_67;
x_3 = x_121;
goto _start;
}
case 2:
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_2);
x_123 = lean_ctor_get(x_116, 0);
lean_inc(x_123);
lean_dec(x_116);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_3);
x_2 = x_67;
x_3 = x_124;
goto _start;
}
case 3:
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_2);
x_126 = lean_ctor_get(x_116, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_116, 1);
lean_inc(x_127);
lean_dec(x_116);
x_68 = x_126;
x_69 = x_127;
goto block_99;
}
default: 
{
lean_object* x_128; 
lean_dec(x_116);
lean_dec(x_67);
x_128 = lean_box(0);
x_9 = x_128;
goto block_62;
}
}
}
block_99:
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
lean_object* x_83; lean_object* x_84; 
x_83 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_84 = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(x_68, x_3, x_83, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_87 = l_Lean_Compiler_LCNF_ToLCNF_bindCases(x_85, x_69, x_4, x_5, x_6, x_7, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_2 = x_67;
x_3 = x_88;
x_8 = x_89;
goto _start;
}
else
{
uint8_t x_91; 
lean_dec(x_67);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_87);
if (x_91 == 0)
{
return x_87;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_87, 0);
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_87);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_84);
if (x_95 == 0)
{
return x_84;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_84, 0);
x_97 = lean_ctor_get(x_84, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_84);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
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
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_array_get_size(x_1);
x_10 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go(x_1, x_9, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_2, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_array_push(x_1, x_16);
x_18 = lean_array_get_size(x_17);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go(x_17, x_18, x_20, x_3, x_4, x_5, x_6, x_15);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__2;
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
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__2;
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
x_1 = lean_unsigned_to_nat(0u);
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
x_1 = lean_unsigned_to_nat(0u);
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
x_5 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, 1, x_1);
lean_ctor_set_uint8(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, 4, x_1);
lean_ctor_set_uint8(x_5, 5, x_2);
lean_ctor_set_uint8(x_5, 6, x_3);
lean_ctor_set_uint8(x_5, 7, x_1);
lean_ctor_set_uint8(x_5, 8, x_3);
lean_ctor_set_uint8(x_5, 9, x_3);
lean_ctor_set_uint8(x_5, 10, x_1);
lean_ctor_set_uint8(x_5, 11, x_3);
lean_ctor_set_uint8(x_5, 12, x_3);
lean_ctor_set_uint8(x_5, 13, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__2;
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
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__2;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__6() {
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
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__2;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__4;
x_3 = l_Lean_Compiler_LCNF_ToLCNF_State_cache___default___closed__1;
x_4 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__7;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__6;
x_3 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__8;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
x_16 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_14);
lean_ctor_set(x_18, 4, x_17);
lean_ctor_set(x_18, 5, x_14);
x_19 = lean_st_ref_get(x_6, x_12);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__9;
x_22 = lean_st_mk_ref(x_21, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_6);
lean_inc(x_23);
x_25 = lean_apply_5(x_1, x_18, x_23, x_5, x_6, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_6, x_27);
lean_dec(x_6);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_get(x_23, x_29);
lean_dec(x_23);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_26);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_23);
lean_dec(x_6);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 4);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode(x_13, x_1, x_3, x_4, x_5, x_6, x_12);
return x_14;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 4);
x_15 = lean_array_push(x_14, x_1);
lean_ctor_set(x_11, 4, x_15);
x_16 = lean_st_ref_set(x_2, x_11, x_12);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get(x_11, 3);
x_27 = lean_ctor_get(x_11, 4);
x_28 = lean_ctor_get(x_11, 5);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_29 = lean_array_push(x_27, x_1);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_29);
lean_ctor_set(x_30, 5, x_28);
x_31 = lean_st_ref_set(x_2, x_30, x_12);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
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
x_17 = l_Lean_Expr_fvar___override(x_16);
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
x_20 = l_Lean_Expr_fvar___override(x_19);
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
uint8_t x_9; 
x_9 = l_Lean_Expr_isFVar(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Compiler_LCNF_mkFreshBinderName(x_2, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_13 = l_Lean_Compiler_LCNF_inferType(x_1, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_mkLetDecl(x_11, x_14, x_1, x_4, x_5, x_6, x_7, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_17);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_pushElement(x_19, x_3, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = l_Lean_Expr_fvar___override(x_23);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
x_27 = l_Lean_Expr_fvar___override(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_8);
return x_33;
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
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__5;
x_3 = l_Lean_Compiler_LCNF_ToLCNF_State_cache___default___closed__1;
x_4 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__1;
x_10 = lean_st_mk_ref(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_11);
x_13 = lean_apply_6(x_1, x_11, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_5, x_15);
lean_dec(x_5);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_11, x_17);
lean_dec(x_11);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_14);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_5);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
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
x_17 = l_Lean_Expr_hash(x_13);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
x_9 = lean_uint64_to_usize(x_8);
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Lean_AssocList_contains___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__2(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_box(x_3);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_11);
x_17 = lean_array_uset(x_6, x_10, x_16);
x_18 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_14);
x_19 = lean_nat_dec_le(x_18, x_7);
lean_dec(x_7);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_1);
x_20 = l_Lean_HashMapImp_expand___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__3(x_14, x_17);
return x_20;
}
else
{
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
x_21 = l_Lean_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6(x_2, x_3, x_11);
x_22 = lean_array_uset(x_6, x_10, x_21);
lean_ctor_set(x_1, 1, x_22);
return x_1;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; size_t x_27; size_t x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_25 = lean_array_get_size(x_24);
x_26 = l_Lean_Expr_hash(x_2);
x_27 = lean_uint64_to_usize(x_26);
x_28 = lean_usize_modn(x_27, x_25);
x_29 = lean_array_uget(x_24, x_28);
x_30 = l_Lean_AssocList_contains___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__2(x_2, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_23, x_31);
lean_dec(x_23);
x_33 = lean_box(x_3);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_29);
x_35 = lean_array_uset(x_24, x_28, x_34);
x_36 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_32);
x_37 = lean_nat_dec_le(x_36, x_25);
lean_dec(x_25);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = l_Lean_HashMapImp_expand___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__3(x_32, x_35);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_25);
x_40 = l_Lean_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6(x_2, x_3, x_29);
x_41 = lean_array_uset(x_24, x_28, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_23);
lean_ctor_set(x_42, 1, x_41);
return x_42;
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
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Lean_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__8(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_3, x_10);
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
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_18);
lean_ctor_set(x_19, 5, x_15);
x_20 = lean_st_ref_get(x_7, x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__9;
x_23 = lean_st_mk_ref(x_22, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_7);
lean_inc(x_24);
lean_inc(x_1);
x_26 = l_Lean_Meta_isTypeFormerType(x_1, x_19, x_24, x_6, x_7, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_7, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_get(x_24, x_30);
lean_dec(x_24);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_st_ref_get(x_7, x_32);
lean_dec(x_7);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_st_ref_take(x_3, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_ctor_get(x_36, 3);
x_40 = lean_unbox(x_27);
x_41 = l_Lean_HashMap_insert___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__1(x_39, x_1, x_40);
lean_ctor_set(x_36, 3, x_41);
x_42 = lean_st_ref_set(x_3, x_36, x_37);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_27);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_27);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_47 = lean_ctor_get(x_36, 0);
x_48 = lean_ctor_get(x_36, 1);
x_49 = lean_ctor_get(x_36, 2);
x_50 = lean_ctor_get(x_36, 3);
x_51 = lean_ctor_get(x_36, 4);
x_52 = lean_ctor_get(x_36, 5);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_36);
x_53 = lean_unbox(x_27);
x_54 = l_Lean_HashMap_insert___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__1(x_50, x_1, x_53);
x_55 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_48);
lean_ctor_set(x_55, 2, x_49);
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 4, x_51);
lean_ctor_set(x_55, 5, x_52);
x_56 = lean_st_ref_set(x_3, x_55, x_37);
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
lean_ctor_set(x_59, 0, x_27);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_26);
if (x_60 == 0)
{
return x_26;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_26, 0);
x_62 = lean_ctor_get(x_26, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_26);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_free_object(x_8);
x_18 = lean_st_ref_get(x_6, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_2, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_22, 3);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_1);
x_25 = l_Lean_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__7(x_24, x_1);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_20);
x_26 = lean_box(0);
x_27 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1(x_1, x_26, x_2, x_3, x_4, x_5, x_6, x_23);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_20, 0, x_28);
return x_20;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_ctor_get(x_29, 3);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_1);
x_32 = l_Lean_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__7(x_31, x_1);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
x_34 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1(x_1, x_33, x_2, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_8, 0);
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_8);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(x_39, x_1);
switch (x_40) {
case 0:
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = 0;
x_42 = lean_box(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
case 1:
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = 1;
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_38);
return x_46;
}
default: 
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_st_ref_get(x_6, x_38);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_st_ref_get(x_2, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_50, 3);
lean_inc(x_53);
lean_dec(x_50);
lean_inc(x_1);
x_54 = l_Lean_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__7(x_53, x_1);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_52);
x_55 = lean_box(0);
x_56 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1(x_1, x_55, x_2, x_3, x_4, x_5, x_6, x_51);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
lean_dec(x_54);
if (lean_is_scalar(x_52)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_52;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_51);
return x_58;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 5);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_st_ref_get(x_6, x_12);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_take(x_2, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_20, 4);
lean_dec(x_23);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
lean_ctor_set(x_20, 4, x_24);
x_25 = lean_st_ref_set(x_2, x_20, x_21);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_6);
lean_inc(x_2);
x_27 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_st_ref_get(x_6, x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_st_ref_get(x_2, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_6, x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_get(x_2, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_33, 2);
lean_inc(x_40);
lean_dec(x_33);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_42 = lean_ctor_get(x_38, 5);
lean_dec(x_42);
x_43 = lean_ctor_get(x_38, 4);
lean_dec(x_43);
x_44 = lean_ctor_get(x_38, 2);
lean_dec(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_38, 0);
lean_dec(x_46);
lean_ctor_set(x_38, 5, x_16);
lean_ctor_set(x_38, 4, x_15);
lean_ctor_set(x_38, 2, x_40);
lean_ctor_set(x_38, 1, x_14);
lean_ctor_set(x_38, 0, x_13);
x_47 = lean_st_ref_get(x_6, x_39);
lean_dec(x_6);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_st_ref_set(x_2, x_38, x_48);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_28);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_28);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_38, 3);
lean_inc(x_54);
lean_dec(x_38);
x_55 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_55, 0, x_13);
lean_ctor_set(x_55, 1, x_14);
lean_ctor_set(x_55, 2, x_40);
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 4, x_15);
lean_ctor_set(x_55, 5, x_16);
x_56 = lean_st_ref_get(x_6, x_39);
lean_dec(x_6);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_st_ref_set(x_2, x_55, x_57);
lean_dec(x_2);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_28);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_62 = lean_ctor_get(x_27, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_27, 1);
lean_inc(x_63);
lean_dec(x_27);
x_64 = lean_st_ref_get(x_6, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_st_ref_get(x_2, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_st_ref_get(x_6, x_68);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_st_ref_get(x_2, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_67, 2);
lean_inc(x_74);
lean_dec(x_67);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_76 = lean_ctor_get(x_72, 5);
lean_dec(x_76);
x_77 = lean_ctor_get(x_72, 4);
lean_dec(x_77);
x_78 = lean_ctor_get(x_72, 2);
lean_dec(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_dec(x_79);
x_80 = lean_ctor_get(x_72, 0);
lean_dec(x_80);
lean_ctor_set(x_72, 5, x_16);
lean_ctor_set(x_72, 4, x_15);
lean_ctor_set(x_72, 2, x_74);
lean_ctor_set(x_72, 1, x_14);
lean_ctor_set(x_72, 0, x_13);
x_81 = lean_st_ref_get(x_6, x_73);
lean_dec(x_6);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_st_ref_set(x_2, x_72, x_82);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_83, 0);
lean_dec(x_85);
lean_ctor_set_tag(x_83, 1);
lean_ctor_set(x_83, 0, x_62);
return x_83;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_62);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_88 = lean_ctor_get(x_72, 3);
lean_inc(x_88);
lean_dec(x_72);
x_89 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_89, 0, x_13);
lean_ctor_set(x_89, 1, x_14);
lean_ctor_set(x_89, 2, x_74);
lean_ctor_set(x_89, 3, x_88);
lean_ctor_set(x_89, 4, x_15);
lean_ctor_set(x_89, 5, x_16);
x_90 = lean_st_ref_get(x_6, x_73);
lean_dec(x_6);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_st_ref_set(x_2, x_89, x_91);
lean_dec(x_2);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_62);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_96 = lean_ctor_get(x_20, 0);
x_97 = lean_ctor_get(x_20, 1);
x_98 = lean_ctor_get(x_20, 2);
x_99 = lean_ctor_get(x_20, 3);
x_100 = lean_ctor_get(x_20, 5);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_20);
x_101 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_102 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_102, 0, x_96);
lean_ctor_set(x_102, 1, x_97);
lean_ctor_set(x_102, 2, x_98);
lean_ctor_set(x_102, 3, x_99);
lean_ctor_set(x_102, 4, x_101);
lean_ctor_set(x_102, 5, x_100);
x_103 = lean_st_ref_set(x_2, x_102, x_21);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
lean_inc(x_6);
lean_inc(x_2);
x_105 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_st_ref_get(x_6, x_107);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_st_ref_get(x_2, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_st_ref_get(x_6, x_112);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_115 = lean_st_ref_get(x_2, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_ctor_get(x_111, 2);
lean_inc(x_118);
lean_dec(x_111);
x_119 = lean_ctor_get(x_116, 3);
lean_inc(x_119);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 lean_ctor_release(x_116, 2);
 lean_ctor_release(x_116, 3);
 lean_ctor_release(x_116, 4);
 lean_ctor_release(x_116, 5);
 x_120 = x_116;
} else {
 lean_dec_ref(x_116);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 6, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_13);
lean_ctor_set(x_121, 1, x_14);
lean_ctor_set(x_121, 2, x_118);
lean_ctor_set(x_121, 3, x_119);
lean_ctor_set(x_121, 4, x_15);
lean_ctor_set(x_121, 5, x_16);
x_122 = lean_st_ref_get(x_6, x_117);
lean_dec(x_6);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_124 = lean_st_ref_set(x_2, x_121, x_123);
lean_dec(x_2);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_126 = x_124;
} else {
 lean_dec_ref(x_124);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_106);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_128 = lean_ctor_get(x_105, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_105, 1);
lean_inc(x_129);
lean_dec(x_105);
x_130 = lean_st_ref_get(x_6, x_129);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_st_ref_get(x_2, x_131);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_st_ref_get(x_6, x_134);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_st_ref_get(x_2, x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_ctor_get(x_133, 2);
lean_inc(x_140);
lean_dec(x_133);
x_141 = lean_ctor_get(x_138, 3);
lean_inc(x_141);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 lean_ctor_release(x_138, 2);
 lean_ctor_release(x_138, 3);
 lean_ctor_release(x_138, 4);
 lean_ctor_release(x_138, 5);
 x_142 = x_138;
} else {
 lean_dec_ref(x_138);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(0, 6, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_13);
lean_ctor_set(x_143, 1, x_14);
lean_ctor_set(x_143, 2, x_140);
lean_ctor_set(x_143, 3, x_141);
lean_ctor_set(x_143, 4, x_15);
lean_ctor_set(x_143, 5, x_16);
x_144 = lean_st_ref_get(x_6, x_139);
lean_dec(x_6);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_st_ref_set(x_2, x_143, x_145);
lean_dec(x_2);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
 lean_ctor_set_tag(x_149, 1);
}
lean_ctor_set(x_149, 0, x_128);
lean_ctor_set(x_149, 1, x_147);
return x_149;
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
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_applyToAny___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_RBNode_findCore___at_Lean_Compiler_LCNF_CompilerM_codeBind_go___spec__1(x_1, x_3);
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
x_6 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___lambda__1___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 5);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_applyToAny___lambda__1___boxed), 2, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = l_Lean_Expr_ReplaceImpl_replaceUnsafe(x_14, x_1);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_ctor_get(x_16, 5);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_applyToAny___lambda__1___boxed), 2, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = l_Lean_Expr_ReplaceImpl_replaceUnsafe(x_19, x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
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
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__2(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
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
x_17 = l_Lean_Expr_hash(x_13);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
x_9 = lean_uint64_to_usize(x_8);
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__4(x_2, x_11);
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
x_17 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_14);
x_18 = lean_nat_dec_le(x_17, x_7);
lean_dec(x_7);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__5(x_14, x_16);
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
x_20 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__8(x_2, x_3, x_11);
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
x_25 = l_Lean_Expr_hash(x_2);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_modn(x_26, x_24);
x_28 = lean_array_uget(x_23, x_27);
x_29 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__4(x_2, x_28);
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
x_34 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_31);
x_35 = lean_nat_dec_le(x_34, x_24);
lean_dec(x_24);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__5(x_31, x_33);
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
x_38 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__8(x_2, x_3, x_28);
x_39 = lean_array_uset(x_23, x_27, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_1);
x_15 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__1(x_14, x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_10);
x_16 = lean_st_ref_get(x_6, x_13);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_2, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
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
x_27 = lean_st_ref_get(x_6, x_20);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__9;
x_30 = lean_st_mk_ref(x_29, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_31);
lean_inc(x_1);
x_33 = l_Lean_Compiler_LCNF_toLCNFType(x_1, x_26, x_31, x_5, x_6, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_get(x_6, x_35);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_st_ref_get(x_31, x_37);
lean_dec(x_31);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny(x_34, x_2, x_3, x_4, x_5, x_6, x_39);
lean_dec(x_5);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_st_ref_get(x_6, x_42);
lean_dec(x_6);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_st_ref_take(x_2, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_46, 2);
lean_inc(x_41);
x_50 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__3(x_49, x_1, x_41);
lean_ctor_set(x_46, 2, x_50);
x_51 = lean_st_ref_set(x_2, x_46, x_47);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set(x_51, 0, x_41);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_41);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_56 = lean_ctor_get(x_46, 0);
x_57 = lean_ctor_get(x_46, 1);
x_58 = lean_ctor_get(x_46, 2);
x_59 = lean_ctor_get(x_46, 3);
x_60 = lean_ctor_get(x_46, 4);
x_61 = lean_ctor_get(x_46, 5);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_46);
lean_inc(x_41);
x_62 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__3(x_58, x_1, x_41);
x_63 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_57);
lean_ctor_set(x_63, 2, x_62);
lean_ctor_set(x_63, 3, x_59);
lean_ctor_set(x_63, 4, x_60);
lean_ctor_set(x_63, 5, x_61);
x_64 = lean_st_ref_set(x_2, x_63, x_47);
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
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_41);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_33);
if (x_68 == 0)
{
return x_33;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_33, 0);
x_70 = lean_ctor_get(x_33, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_33);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_72 = lean_ctor_get(x_15, 0);
lean_inc(x_72);
lean_dec(x_15);
lean_ctor_set(x_10, 0, x_72);
return x_10;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_10, 0);
x_74 = lean_ctor_get(x_10, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_10);
x_75 = lean_ctor_get(x_73, 2);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_1);
x_76 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__1(x_75, x_1);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_77 = lean_st_ref_get(x_6, x_74);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_st_ref_get(x_2, x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_box(0);
x_84 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
x_85 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_82);
lean_ctor_set(x_87, 2, x_85);
lean_ctor_set(x_87, 3, x_83);
lean_ctor_set(x_87, 4, x_86);
lean_ctor_set(x_87, 5, x_83);
x_88 = lean_st_ref_get(x_6, x_81);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__9;
x_91 = lean_st_mk_ref(x_90, x_89);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_92);
lean_inc(x_1);
x_94 = l_Lean_Compiler_LCNF_toLCNFType(x_1, x_87, x_92, x_5, x_6, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_st_ref_get(x_6, x_96);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_st_ref_get(x_92, x_98);
lean_dec(x_92);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny(x_95, x_2, x_3, x_4, x_5, x_6, x_100);
lean_dec(x_5);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_st_ref_get(x_6, x_103);
lean_dec(x_6);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_st_ref_take(x_2, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_107, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_107, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 4);
lean_inc(x_113);
x_114 = lean_ctor_get(x_107, 5);
lean_inc(x_114);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 lean_ctor_release(x_107, 3);
 lean_ctor_release(x_107, 4);
 lean_ctor_release(x_107, 5);
 x_115 = x_107;
} else {
 lean_dec_ref(x_107);
 x_115 = lean_box(0);
}
lean_inc(x_102);
x_116 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__3(x_111, x_1, x_102);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 6, 0);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_109);
lean_ctor_set(x_117, 1, x_110);
lean_ctor_set(x_117, 2, x_116);
lean_ctor_set(x_117, 3, x_112);
lean_ctor_set(x_117, 4, x_113);
lean_ctor_set(x_117, 5, x_114);
x_118 = lean_st_ref_set(x_2, x_117, x_108);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_102);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_92);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_122 = lean_ctor_get(x_94, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_94, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_124 = x_94;
} else {
 lean_dec_ref(x_94);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_126 = lean_ctor_get(x_76, 0);
lean_inc(x_126);
lean_dec(x_76);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_74);
return x_127;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_10);
x_16 = l_Lean_Compiler_LCNF_mkParam(x_10, x_14, x_12, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_7, x_18);
lean_dec(x_7);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_take(x_3, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
x_27 = 0;
x_28 = lean_local_ctx_mk_local_decl(x_25, x_26, x_10, x_2, x_27);
lean_ctor_set(x_22, 0, x_28);
x_29 = lean_st_ref_set(x_3, x_22, x_23);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_17);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_17);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
x_36 = lean_ctor_get(x_22, 2);
x_37 = lean_ctor_get(x_22, 3);
x_38 = lean_ctor_get(x_22, 4);
x_39 = lean_ctor_get(x_22, 5);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_40 = lean_ctor_get(x_17, 0);
lean_inc(x_40);
x_41 = 0;
x_42 = lean_local_ctx_mk_local_decl(x_34, x_40, x_10, x_2, x_41);
x_43 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_35);
lean_ctor_set(x_43, 2, x_36);
lean_ctor_set(x_43, 3, x_37);
lean_ctor_set(x_43, 4, x_38);
lean_ctor_set(x_43, 5, x_39);
x_44 = lean_st_ref_set(x_3, x_43, x_23);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_12 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(x_1, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = l_Lean_Compiler_LCNF_mkLetDecl(x_13, x_4, x_5, x_7, x_8, x_9, x_10, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_10, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_take(x_6, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 4);
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
x_27 = 0;
x_28 = lean_local_ctx_mk_let_decl(x_24, x_26, x_13, x_2, x_3, x_27);
lean_inc(x_16);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_16);
x_30 = lean_array_push(x_25, x_29);
lean_ctor_set(x_21, 4, x_30);
lean_ctor_set(x_21, 0, x_28);
x_31 = lean_st_ref_set(x_6, x_21, x_22);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_16);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_16);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
x_38 = lean_ctor_get(x_21, 2);
x_39 = lean_ctor_get(x_21, 3);
x_40 = lean_ctor_get(x_21, 4);
x_41 = lean_ctor_get(x_21, 5);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_42 = lean_ctor_get(x_16, 0);
lean_inc(x_42);
x_43 = 0;
x_44 = lean_local_ctx_mk_let_decl(x_36, x_42, x_13, x_2, x_3, x_43);
lean_inc(x_16);
x_45 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_45, 0, x_16);
x_46 = lean_array_push(x_40, x_45);
x_47 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_37);
lean_ctor_set(x_47, 2, x_38);
lean_ctor_set(x_47, 3, x_39);
lean_ctor_set(x_47, 4, x_46);
lean_ctor_set(x_47, 5, x_41);
x_48 = lean_st_ref_set(x_6, x_47, x_22);
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
lean_ctor_set(x_51, 0, x_16);
lean_ctor_set(x_51, 1, x_49);
return x_51;
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Compiler_LCNF_ToLCNF_etaExpandN___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Compiler_LCNF_ToLCNF_etaExpandN___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at_Lean_Compiler_LCNF_ToLCNF_etaExpandN___spec__1___rarg), 8, 0);
return x_2;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_11 = lean_st_ref_get(x_7, x_8);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
x_19 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_20 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_17);
lean_ctor_set(x_20, 4, x_9);
lean_ctor_set(x_20, 5, x_17);
x_21 = lean_st_ref_get(x_7, x_15);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__9;
x_24 = lean_st_mk_ref(x_23, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_25);
lean_inc(x_20);
lean_inc(x_1);
x_27 = lean_infer_type(x_1, x_20, x_25, x_6, x_7, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_2);
x_31 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___lambda__1___boxed), 8, 1);
lean_closure_set(x_31, 0, x_1);
lean_inc(x_7);
lean_inc(x_25);
x_32 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Compiler_LCNF_ToLCNF_etaExpandN___spec__1___rarg(x_28, x_30, x_31, x_20, x_25, x_6, x_7, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_7, x_34);
lean_dec(x_7);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_get(x_25, x_36);
lean_dec(x_25);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_33);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_25);
lean_dec(x_7);
x_42 = !lean_is_exclusive(x_32);
if (x_42 == 0)
{
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_32);
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
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_27);
if (x_46 == 0)
{
return x_27;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_27, 0);
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_27);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_8);
return x_50;
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
x_21 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_390_(x_5, x_5);
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
x_34 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_390_(x_5, x_5);
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
x_44 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_390_(x_5, x_5);
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
x_54 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_390_(x_5, x_5);
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
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__2;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__3;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__4;
x_9 = lean_panic_fn(x_8, x_1);
x_10 = lean_apply_6(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_19 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__6;
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
x_21 = lean_alloc_ctor(6, 2, 0);
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
x_28 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__6;
lean_inc(x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
x_30 = lean_alloc_ctor(6, 2, 0);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__8(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_23 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Expr_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__8(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10___closed__2;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_take(x_3, x_10);
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
lean_inc(x_2);
x_16 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__1(x_15, x_1, x_2);
lean_ctor_set(x_12, 1, x_16);
x_17 = lean_st_ref_set(x_3, x_12, x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_2);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
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
lean_inc(x_2);
x_28 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__1(x_23, x_1, x_2);
x_29 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
lean_ctor_set(x_29, 5, x_27);
x_30 = lean_st_ref_set(x_3, x_29, x_13);
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
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_31);
return x_33;
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
x_3 = lean_unsigned_to_nat(412u);
x_4 = lean_unsigned_to_nat(24u);
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected occurrence of metavariable in code generator", 55);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__2;
x_3 = lean_unsigned_to_nat(410u);
x_4 = lean_unsigned_to_nat(24u);
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
case 0:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__4;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_9, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_st_ref_get(x_7, x_8);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_3, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 5);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_RBNode_findCore___at_Lean_Compiler_LCNF_CompilerM_codeBind_go___spec__1(x_24, x_18);
lean_dec(x_18);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_inc(x_1);
x_26 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_1, x_3, x_4, x_5, x_6, x_7, x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_25);
x_27 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_28 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_27, x_3, x_4, x_5, x_6, x_7, x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_28;
}
}
case 2:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = l_Lean_indentExpr(x_1);
x_30 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__6;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__8;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6(x_33, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
case 3:
{
lean_object* x_39; 
lean_inc(x_1);
x_39 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_39;
}
case 6:
{
lean_object* x_40; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_40 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_41, x_3, x_4, x_5, x_6, x_7, x_42);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 7:
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__9;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_49 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_48, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_50, x_3, x_4, x_5, x_6, x_7, x_51);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_49);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
case 8:
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_58 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(x_1, x_57, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_59, x_3, x_4, x_5, x_6, x_7, x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
return x_58;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_58, 0);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_58);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
case 9:
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_67 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_1, x_66, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_68, x_3, x_4, x_5, x_6, x_7, x_69);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_70;
}
else
{
uint8_t x_71; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_67);
if (x_71 == 0)
{
return x_67;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_67, 0);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_67);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
case 10:
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_1, 1);
lean_inc(x_75);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_76 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_75, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_77, x_3, x_4, x_5, x_6, x_7, x_78);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_79;
}
else
{
uint8_t x_80; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_76);
if (x_80 == 0)
{
return x_76;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_76, 0);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_76);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
case 11:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_1, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_1, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_1, 2);
lean_inc(x_86);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_87 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(x_84, x_85, x_86, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_88, x_3, x_4, x_5, x_6, x_7, x_89);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_90;
}
else
{
uint8_t x_91; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_87);
if (x_91 == 0)
{
return x_87;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_87, 0);
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_87);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
default: 
{
lean_object* x_95; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_95 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_96, x_3, x_4, x_5, x_6, x_7, x_97);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_98;
}
else
{
uint8_t x_99; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
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
x_19 = lean_nat_dec_eq(x_11, x_12);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_5);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_21 = lean_ctor_get(x_5, 10);
lean_dec(x_21);
x_22 = lean_ctor_get(x_5, 9);
lean_dec(x_22);
x_23 = lean_ctor_get(x_5, 8);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 7);
lean_dec(x_24);
x_25 = lean_ctor_get(x_5, 6);
lean_dec(x_25);
x_26 = lean_ctor_get(x_5, 5);
lean_dec(x_26);
x_27 = lean_ctor_get(x_5, 4);
lean_dec(x_27);
x_28 = lean_ctor_get(x_5, 3);
lean_dec(x_28);
x_29 = lean_ctor_get(x_5, 2);
lean_dec(x_29);
x_30 = lean_ctor_get(x_5, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_5, 0);
lean_dec(x_31);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_11, x_32);
lean_dec(x_11);
lean_ctor_set(x_5, 3, x_33);
x_34 = lean_st_ref_get(x_6, x_7);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_get(x_2, x_35);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_1);
x_41 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__7(x_40, x_1);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_free_object(x_36);
x_42 = lean_box(0);
x_43 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2(x_1, x_42, x_2, x_3, x_4, x_5, x_6, x_39);
return x_43;
}
else
{
lean_object* x_44; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec(x_41);
lean_ctor_set(x_36, 0, x_44);
return x_36;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_36, 0);
x_46 = lean_ctor_get(x_36, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_36);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_1);
x_48 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__7(x_47, x_1);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_box(0);
x_50 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2(x_1, x_49, x_2, x_3, x_4, x_5, x_6, x_46);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_5);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_46);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_5);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_11, x_53);
lean_dec(x_11);
x_55 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_55, 0, x_8);
lean_ctor_set(x_55, 1, x_9);
lean_ctor_set(x_55, 2, x_10);
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 4, x_12);
lean_ctor_set(x_55, 5, x_13);
lean_ctor_set(x_55, 6, x_14);
lean_ctor_set(x_55, 7, x_15);
lean_ctor_set(x_55, 8, x_16);
lean_ctor_set(x_55, 9, x_17);
lean_ctor_set(x_55, 10, x_18);
x_56 = lean_st_ref_get(x_6, x_7);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_st_ref_get(x_2, x_57);
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
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
lean_inc(x_1);
x_63 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__7(x_62, x_1);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_61);
x_64 = lean_box(0);
x_65 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2(x_1, x_64, x_2, x_3, x_4, x_55, x_6, x_60);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_55);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
lean_dec(x_63);
if (lean_is_scalar(x_61)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_61;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_60);
return x_67;
}
}
}
else
{
lean_object* x_68; 
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
x_68 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10(x_13, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_68;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
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
x_48 = lean_st_ref_get(x_7, x_8);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_st_ref_get(x_3, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_box(0);
x_55 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
x_56 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_53);
lean_ctor_set(x_58, 2, x_56);
lean_ctor_set(x_58, 3, x_54);
lean_ctor_set(x_58, 4, x_57);
lean_ctor_set(x_58, 5, x_54);
x_59 = lean_st_ref_get(x_7, x_52);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__9;
x_62 = lean_st_mk_ref(x_61, x_60);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_63);
lean_inc(x_13);
x_65 = l_Lean_Meta_isProp(x_13, x_58, x_63, x_6, x_7, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_st_ref_get(x_7, x_67);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_st_ref_get(x_63, x_69);
lean_dec(x_63);
x_71 = lean_unbox(x_66);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_66);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
x_73 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(x_13, x_3, x_4, x_5, x_6, x_7, x_72);
x_15 = x_73;
goto block_47;
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_70);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_70, 0);
lean_dec(x_75);
lean_ctor_set(x_70, 0, x_66);
x_15 = x_70;
goto block_47;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_dec(x_70);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_66);
lean_ctor_set(x_77, 1, x_76);
x_15 = x_77;
goto block_47;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_63);
x_78 = !lean_is_exclusive(x_65);
if (x_78 == 0)
{
x_15 = x_65;
goto block_47;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_65, 0);
x_80 = lean_ctor_get(x_65, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_65);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_15 = x_81;
goto block_47;
}
}
block_47:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
x_19 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_13, x_3, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_14);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_14, x_3, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(x_9, x_13, x_14, x_20, x_23, x_3, x_4, x_5, x_6, x_7, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Expr_fvar___override(x_28);
x_30 = lean_array_push(x_2, x_29);
x_1 = x_12;
x_2 = x_30;
x_8 = x_27;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_20);
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
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
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
x_36 = !lean_is_exclusive(x_19);
if (x_36 == 0)
{
return x_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_19, 0);
x_38 = lean_ctor_get(x_19, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_19);
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
lean_dec(x_13);
lean_dec(x_9);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_array_push(x_2, x_14);
x_1 = x_12;
x_2 = x_41;
x_8 = x_40;
goto _start;
}
}
else
{
uint8_t x_43; 
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
x_43 = !lean_is_exclusive(x_15);
if (x_43 == 0)
{
return x_15;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_15, 0);
x_45 = lean_ctor_get(x_15, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_15);
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
lean_object* x_82; lean_object* x_83; 
x_82 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_83 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_82, x_3, x_4, x_5, x_6, x_7, x_8);
return x_83;
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
x_17 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_Compiler_LCNF_erasedExpr;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_3, x_10);
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
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_18);
lean_ctor_set(x_19, 5, x_15);
x_20 = lean_st_ref_get(x_7, x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__9;
x_23 = lean_st_mk_ref(x_22, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_24);
lean_inc(x_1);
x_26 = lean_infer_type(x_1, x_19, x_24, x_6, x_7, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_7, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_get(x_24, x_30);
lean_dec(x_24);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_st_ref_get(x_7, x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_st_ref_get(x_3, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_16);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_17);
lean_ctor_set(x_39, 3, x_15);
lean_ctor_set(x_39, 4, x_18);
lean_ctor_set(x_39, 5, x_15);
x_40 = lean_st_ref_get(x_7, x_37);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_st_mk_ref(x_22, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_43);
lean_inc(x_27);
x_45 = l_Lean_Meta_isProp(x_27, x_39, x_43, x_6, x_7, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_st_ref_get(x_7, x_47);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_st_ref_get(x_43, x_49);
lean_dec(x_43);
x_51 = lean_unbox(x_46);
lean_dec(x_46);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_box(0);
x_54 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2(x_27, x_1, x_53, x_3, x_4, x_5, x_6, x_7, x_52);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_50, 0);
lean_dec(x_56);
x_57 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_50, 0, x_57);
return x_50;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_dec(x_50);
x_59 = l_Lean_Compiler_LCNF_erasedExpr;
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_45);
if (x_61 == 0)
{
return x_45;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_45, 0);
x_63 = lean_ctor_get(x_45, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_45);
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
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_26);
if (x_65 == 0)
{
return x_26;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_26, 0);
x_67 = lean_ctor_get(x_26, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_26);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
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
x_20 = lean_nat_dec_eq(x_12, x_13);
if (x_8 == 0)
{
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
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
x_34 = lean_nat_add(x_12, x_33);
lean_dec(x_12);
lean_ctor_set(x_5, 3, x_34);
x_35 = lean_box(0);
x_36 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__3(x_1, x_35, x_2, x_3, x_4, x_5, x_6, x_7);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_12, x_37);
lean_dec(x_12);
x_39 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_39, 0, x_9);
lean_ctor_set(x_39, 1, x_10);
lean_ctor_set(x_39, 2, x_11);
lean_ctor_set(x_39, 3, x_38);
lean_ctor_set(x_39, 4, x_13);
lean_ctor_set(x_39, 5, x_14);
lean_ctor_set(x_39, 6, x_15);
lean_ctor_set(x_39, 7, x_16);
lean_ctor_set(x_39, 8, x_17);
lean_ctor_set(x_39, 9, x_18);
lean_ctor_set(x_39, 10, x_19);
x_40 = lean_box(0);
x_41 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__3(x_1, x_40, x_2, x_3, x_4, x_39, x_6, x_7);
return x_41;
}
}
else
{
lean_object* x_42; 
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
x_42 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10(x_14, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_42;
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
if (x_20 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = l_Lean_Compiler_LCNF_erasedExpr;
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_7);
return x_44;
}
else
{
lean_object* x_45; 
x_45 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10(x_14, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_45;
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
x_25 = l_Lean_Expr_fvar___override(x_24);
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
x_28 = l_Lean_Expr_fvar___override(x_27);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___rarg), 7, 0);
return x_2;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_proj___override(x_1, x_2, x_11);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
x_15 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_4);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault(x_17, x_2, x_4, x_5, x_6, x_7, x_8, x_18);
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
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Quot", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lift", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mk", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("casesOn", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__3;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rec", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__3;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("And", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("False", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Empty", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6;
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
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3;
x_11 = lean_name_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5;
x_13 = lean_name_eq(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7;
x_15 = lean_name_eq(x_9, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9;
x_17 = lean_name_eq(x_9, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__5;
x_19 = lean_name_eq(x_9, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11;
x_21 = lean_name_eq(x_9, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12;
x_23 = lean_name_eq(x_9, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__14;
x_25 = lean_name_eq(x_9, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__16;
x_27 = lean_name_eq(x_9, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17;
x_29 = lean_name_eq(x_9, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__18;
x_31 = lean_name_eq(x_9, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_9);
x_32 = l_Lean_Compiler_LCNF_getCasesInfo_x3f(x_9, x_5, x_6, x_7);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_9);
x_35 = l_Lean_Compiler_LCNF_getCtorArity_x3f(x_9, x_5, x_6, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_st_ref_get(x_6, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1;
lean_inc(x_9);
x_43 = l_Lean_TagDeclarationExtension_isTagged(x_42, x_41, x_9);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2(x_9, x_2, x_3, x_4, x_5, x_6, x_40);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_47);
x_49 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
lean_inc(x_48);
x_50 = lean_mk_array(x_48, x_49);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_sub(x_48, x_51);
lean_dec(x_48);
x_53 = l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__3(x_1, x_50, x_52, x_2, x_3, x_4, x_5, x_6, x_46);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_dec(x_44);
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
lean_dec(x_45);
x_56 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(x_55, x_1, x_2, x_3, x_4, x_5, x_6, x_54);
return x_56;
}
}
else
{
lean_object* x_57; 
lean_dec(x_9);
x_57 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion(x_1, x_2, x_3, x_4, x_5, x_6, x_40);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_9);
x_58 = lean_ctor_get(x_35, 1);
lean_inc(x_58);
lean_dec(x_35);
x_59 = lean_ctor_get(x_36, 0);
lean_inc(x_59);
lean_dec(x_36);
x_60 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(x_59, x_1, x_2, x_3, x_4, x_5, x_6, x_58);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_35);
if (x_61 == 0)
{
return x_35;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_35, 0);
x_63 = lean_ctor_get(x_35, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_35);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_9);
x_65 = lean_ctor_get(x_32, 1);
lean_inc(x_65);
lean_dec(x_32);
x_66 = lean_ctor_get(x_33, 0);
lean_inc(x_66);
lean_dec(x_33);
x_67 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(x_66, x_1, x_2, x_3, x_4, x_5, x_6, x_65);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_32);
if (x_68 == 0)
{
return x_32;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_32, 0);
x_70 = lean_ctor_get(x_32, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_32);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; 
lean_dec(x_9);
x_72 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_72;
}
}
else
{
lean_object* x_73; 
lean_dec(x_9);
x_73 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_73;
}
}
else
{
lean_object* x_74; 
lean_dec(x_9);
x_74 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_74;
}
}
else
{
lean_object* x_75; 
lean_dec(x_9);
x_75 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_75;
}
}
else
{
lean_object* x_76; 
lean_dec(x_9);
x_76 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_76;
}
}
else
{
lean_object* x_77; 
lean_dec(x_9);
x_77 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_77;
}
}
else
{
lean_object* x_78; 
lean_dec(x_9);
x_78 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_9);
x_79 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_79;
}
}
else
{
lean_object* x_80; 
lean_dec(x_9);
x_80 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_9);
x_81 = lean_unsigned_to_nat(3u);
x_82 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(x_81, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_82;
}
}
else
{
lean_object* x_83; 
lean_dec(x_9);
x_83 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_8);
x_84 = lean_unsigned_to_nat(0u);
x_85 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_84);
x_86 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
lean_inc(x_85);
x_87 = lean_mk_array(x_85, x_86);
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_sub(x_85, x_88);
lean_dec(x_85);
x_90 = l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__1(x_1, x_87, x_89, x_2, x_3, x_4, x_5, x_6, x_7);
return x_90;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Expr_isErased(x_1);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault___spec__1(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_mkAppN(x_1, x_14);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
x_18 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_3);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
lean_object* x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_8);
return x_23;
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
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_22 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = l_Lean_Compiler_LCNF_isPredicateType(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_2, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_27 = l_Lean_Compiler_LCNF_erasedExpr;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
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
lean_dec(x_4);
lean_dec(x_2);
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
}
else
{
uint8_t x_33; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_10);
if (x_33 == 0)
{
return x_10;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_10, 0);
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_10);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_3, x_10);
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
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_18);
lean_ctor_set(x_19, 5, x_15);
x_20 = lean_st_ref_get(x_7, x_13);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__9;
x_23 = lean_st_mk_ref(x_22, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_24);
lean_inc(x_1);
x_26 = lean_infer_type(x_1, x_19, x_24, x_6, x_7, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_7, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_get(x_24, x_30);
lean_dec(x_24);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_st_ref_get(x_7, x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_st_ref_get(x_3, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_16);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_17);
lean_ctor_set(x_39, 3, x_15);
lean_ctor_set(x_39, 4, x_18);
lean_ctor_set(x_39, 5, x_15);
x_40 = lean_st_ref_get(x_7, x_37);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_st_mk_ref(x_22, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_43);
lean_inc(x_27);
x_45 = l_Lean_Meta_isProp(x_27, x_39, x_43, x_6, x_7, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_st_ref_get(x_7, x_47);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_st_ref_get(x_43, x_49);
lean_dec(x_43);
x_51 = lean_unbox(x_46);
lean_dec(x_46);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_box(0);
x_54 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg___lambda__1(x_27, x_1, x_53, x_3, x_4, x_5, x_6, x_7, x_52);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_50, 0);
lean_dec(x_56);
x_57 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_50, 0, x_57);
return x_50;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_dec(x_50);
x_59 = l_Lean_Compiler_LCNF_erasedExpr;
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_45);
if (x_61 == 0)
{
return x_45;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_45, 0);
x_63 = lean_ctor_get(x_45, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_45);
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
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_26);
if (x_65 == 0)
{
return x_26;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_26, 0);
x_67 = lean_ctor_get(x_26, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_26);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
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
x_11 = l_Lean_Compiler_LCNF_erasedExpr;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
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
x_19 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__6;
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
x_21 = lean_alloc_ctor(6, 2, 0);
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
x_28 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__6;
lean_inc(x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
x_30 = lean_alloc_ctor(6, 2, 0);
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
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__4;
x_20 = lean_alloc_ctor(10, 2, 0);
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
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__2;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__4;
x_33 = lean_alloc_ctor(10, 2, 0);
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
x_3 = lean_unsigned_to_nat(640u);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Core_instantiateValueLevelParams(x_17, x_15, x_6, x_7, x_18);
lean_dec(x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_22);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
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
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_13);
lean_dec(x_2);
x_35 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__2;
x_36 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_35, x_3, x_4, x_5, x_6, x_7, x_8);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_unsigned_to_nat(0u);
x_38 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_37);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
lean_dec(x_1);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_39, x_40);
lean_dec(x_39);
x_42 = lean_nat_dec_lt(x_38, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_41);
x_43 = l_Lean_Expr_getAppFn(x_2);
x_44 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
lean_inc(x_38);
x_45 = lean_mk_array(x_38, x_44);
x_46 = lean_nat_sub(x_38, x_40);
lean_dec(x_38);
x_47 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_45, x_46);
x_48 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault(x_43, x_47, x_3, x_4, x_5, x_6, x_7, x_8);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_nat_sub(x_41, x_38);
lean_dec(x_38);
lean_dec(x_41);
lean_inc(x_7);
lean_inc(x_6);
x_50 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(x_2, x_49, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_51, x_3, x_4, x_5, x_6, x_7, x_52);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_50);
if (x_54 == 0)
{
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_50, 0);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_50);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
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
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_add(x_1, x_14);
lean_dec(x_1);
x_16 = lean_nat_dec_lt(x_15, x_2);
x_17 = lean_st_ref_get(x_12, x_13);
if (x_16 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_15);
x_100 = lean_ctor_get(x_17, 1);
lean_inc(x_100);
lean_dec(x_17);
x_101 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_102 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_101);
x_18 = x_102;
x_19 = x_100;
goto block_99;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_17, 1);
lean_inc(x_103);
lean_dec(x_17);
x_104 = lean_array_fget(x_6, x_15);
lean_dec(x_15);
x_18 = x_104;
x_19 = x_103;
goto block_99;
}
block_99:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_20 = lean_st_ref_get(x_8, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
x_26 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_28, 4, x_27);
lean_ctor_set(x_28, 5, x_24);
x_29 = lean_st_ref_get(x_12, x_22);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__9;
x_32 = lean_st_mk_ref(x_31, x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_33);
x_35 = lean_whnf(x_18, x_28, x_33, x_11, x_12, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_st_ref_get(x_12, x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_st_ref_get(x_33, x_39);
lean_dec(x_33);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Expr_toCtorIfLit(x_7);
x_43 = l_Lean_Expr_toCtorIfLit(x_36);
x_44 = lean_st_ref_get(x_12, x_41);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_st_ref_get(x_12, x_46);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Expr_isConstructorApp_x3f(x_47, x_42);
lean_dec(x_42);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_51);
lean_dec(x_43);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_53 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_53, 0, x_3);
x_54 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__2;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__4;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6(x_57, x_8, x_9, x_10, x_11, x_12, x_50);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
lean_dec(x_52);
x_60 = l_Lean_Expr_isConstructorApp_x3f(x_51, x_43);
lean_dec(x_43);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_59);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_61 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_61, 0, x_3);
x_62 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__2;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__4;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6(x_65, x_8, x_9, x_10, x_11, x_12, x_50);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_3);
x_67 = lean_ctor_get(x_60, 0);
lean_inc(x_67);
lean_dec(x_60);
x_68 = lean_ctor_get(x_59, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_name_eq(x_69, x_71);
lean_dec(x_71);
lean_dec(x_69);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_59);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_73 = l_Lean_Compiler_LCNF_inferType(x_4, x_9, x_10, x_11, x_12, x_50);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_74, x_8, x_9, x_10, x_11, x_12, x_75);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_76;
}
else
{
uint8_t x_77; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_77 = !lean_is_exclusive(x_73);
if (x_77 == 0)
{
return x_73;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_73, 0);
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_73);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_add(x_5, x_81);
x_83 = lean_nat_dec_lt(x_5, x_2);
lean_dec(x_2);
x_84 = lean_ctor_get(x_59, 4);
lean_inc(x_84);
lean_dec(x_59);
lean_inc(x_82);
lean_inc(x_6);
x_85 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__1), 9, 2);
lean_closure_set(x_85, 0, x_6);
lean_closure_set(x_85, 1, x_82);
if (x_83 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_6);
lean_dec(x_5);
x_86 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_87 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_86);
x_88 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___boxed), 8, 2);
lean_closure_set(x_88, 0, x_87);
lean_closure_set(x_88, 1, x_84);
x_89 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_89, 0, x_88);
lean_closure_set(x_89, 1, x_85);
x_90 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_4, x_82, x_89, x_8, x_9, x_10, x_11, x_12, x_50);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_array_fget(x_6, x_5);
lean_dec(x_5);
lean_dec(x_6);
x_92 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___boxed), 8, 2);
lean_closure_set(x_92, 0, x_91);
lean_closure_set(x_92, 1, x_84);
x_93 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_93, 0, x_92);
lean_closure_set(x_93, 1, x_85);
x_94 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_4, x_82, x_93, x_8, x_9, x_10, x_11, x_12, x_50);
return x_94;
}
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_33);
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
x_95 = !lean_is_exclusive(x_35);
if (x_95 == 0)
{
return x_35;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_35, 0);
x_97 = lean_ctor_get(x_35, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_35);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
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
x_3 = lean_unsigned_to_nat(597u);
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
x_3 = lean_unsigned_to_nat(599u);
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
x_25 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
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
x_32 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_33 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_32);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_array_push(x_4, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_6, x_5);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_4, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_28; uint8_t x_29; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_4, x_18);
lean_dec(x_4);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_28, 1);
x_33 = lean_ctor_get(x_8, 1);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_8);
x_20 = x_35;
x_21 = x_14;
goto block_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_28, 1, x_38);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_8);
x_20 = x_39;
x_21 = x_14;
goto block_27;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_28, 1);
x_41 = lean_ctor_get(x_8, 0);
lean_inc(x_41);
lean_dec(x_8);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_44 = x_40;
} else {
 lean_dec_ref(x_40);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_28, 1, x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_28);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_20 = x_47;
x_21 = x_14;
goto block_27;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_8);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_28, 1);
x_50 = lean_ctor_get(x_8, 0);
x_51 = lean_ctor_get(x_8, 1);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
x_55 = lean_ctor_get(x_30, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_30, 1);
lean_inc(x_56);
lean_dec(x_30);
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_50, 2);
lean_inc(x_59);
x_60 = lean_nat_dec_lt(x_58, x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_55);
lean_ctor_set(x_28, 0, x_56);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_8);
x_20 = x_61;
x_21 = x_14;
goto block_27;
}
else
{
uint8_t x_62; 
lean_free_object(x_49);
lean_free_object(x_8);
lean_free_object(x_28);
x_62 = !lean_is_exclusive(x_50);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_50, 2);
lean_dec(x_63);
x_64 = lean_ctor_get(x_50, 1);
lean_dec(x_64);
x_65 = lean_ctor_get(x_50, 0);
lean_dec(x_65);
x_66 = lean_array_fget(x_57, x_58);
x_67 = lean_nat_add(x_58, x_18);
lean_dec(x_58);
lean_ctor_set(x_50, 1, x_67);
x_68 = lean_nat_dec_lt(x_5, x_2);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_inc(x_3);
x_69 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_70 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_55, x_66, x_69, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_54);
x_75 = l_Lean_Compiler_LCNF_compatibleTypes(x_73, x_54, x_10, x_11, x_12, x_13, x_72);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_54);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_80 = lean_box(0);
x_81 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_74, x_56, x_50, x_53, x_79, x_80, x_9, x_10, x_11, x_12, x_13, x_78);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_20 = x_82;
x_21 = x_83;
goto block_27;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_75, 1);
lean_inc(x_84);
lean_dec(x_75);
x_85 = lean_box(0);
x_86 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_74, x_56, x_50, x_53, x_54, x_85, x_9, x_10, x_11, x_12, x_13, x_84);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_20 = x_87;
x_21 = x_88;
goto block_27;
}
}
else
{
uint8_t x_89; 
lean_dec(x_74);
lean_dec(x_50);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_89 = !lean_is_exclusive(x_75);
if (x_89 == 0)
{
return x_75;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_75, 0);
x_91 = lean_ctor_get(x_75, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_75);
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
lean_dec(x_50);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_93 = !lean_is_exclusive(x_70);
if (x_93 == 0)
{
return x_70;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_70, 0);
x_95 = lean_ctor_get(x_70, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_70);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_array_fget(x_1, x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_98 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_55, x_66, x_97, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_54);
x_103 = l_Lean_Compiler_LCNF_compatibleTypes(x_101, x_54, x_10, x_11, x_12, x_13, x_100);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_54);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_108 = lean_box(0);
x_109 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_102, x_56, x_50, x_53, x_107, x_108, x_9, x_10, x_11, x_12, x_13, x_106);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_20 = x_110;
x_21 = x_111;
goto block_27;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_103, 1);
lean_inc(x_112);
lean_dec(x_103);
x_113 = lean_box(0);
x_114 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_102, x_56, x_50, x_53, x_54, x_113, x_9, x_10, x_11, x_12, x_13, x_112);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_20 = x_115;
x_21 = x_116;
goto block_27;
}
}
else
{
uint8_t x_117; 
lean_dec(x_102);
lean_dec(x_50);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_117 = !lean_is_exclusive(x_103);
if (x_117 == 0)
{
return x_103;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_103, 0);
x_119 = lean_ctor_get(x_103, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_103);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_50);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_121 = !lean_is_exclusive(x_98);
if (x_121 == 0)
{
return x_98;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_98, 0);
x_123 = lean_ctor_get(x_98, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_98);
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
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_50);
x_125 = lean_array_fget(x_57, x_58);
x_126 = lean_nat_add(x_58, x_18);
lean_dec(x_58);
x_127 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_127, 0, x_57);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_127, 2, x_59);
x_128 = lean_nat_dec_lt(x_5, x_2);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
lean_inc(x_3);
x_129 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_130 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_55, x_125, x_129, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
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
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_54);
x_135 = l_Lean_Compiler_LCNF_compatibleTypes(x_133, x_54, x_10, x_11, x_12, x_13, x_132);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_unbox(x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_54);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_140 = lean_box(0);
x_141 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_134, x_56, x_127, x_53, x_139, x_140, x_9, x_10, x_11, x_12, x_13, x_138);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_20 = x_142;
x_21 = x_143;
goto block_27;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_135, 1);
lean_inc(x_144);
lean_dec(x_135);
x_145 = lean_box(0);
x_146 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_134, x_56, x_127, x_53, x_54, x_145, x_9, x_10, x_11, x_12, x_13, x_144);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_20 = x_147;
x_21 = x_148;
goto block_27;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_134);
lean_dec(x_127);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_149 = lean_ctor_get(x_135, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_135, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_151 = x_135;
} else {
 lean_dec_ref(x_135);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_127);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_153 = lean_ctor_get(x_130, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_130, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_155 = x_130;
} else {
 lean_dec_ref(x_130);
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
lean_object* x_157; lean_object* x_158; 
x_157 = lean_array_fget(x_1, x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_158 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_55, x_125, x_157, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_ctor_get(x_159, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
lean_dec(x_159);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_54);
x_163 = l_Lean_Compiler_LCNF_compatibleTypes(x_161, x_54, x_10, x_11, x_12, x_13, x_160);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; uint8_t x_165; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_unbox(x_164);
lean_dec(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_54);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
x_167 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_168 = lean_box(0);
x_169 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_162, x_56, x_127, x_53, x_167, x_168, x_9, x_10, x_11, x_12, x_13, x_166);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_20 = x_170;
x_21 = x_171;
goto block_27;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_163, 1);
lean_inc(x_172);
lean_dec(x_163);
x_173 = lean_box(0);
x_174 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_162, x_56, x_127, x_53, x_54, x_173, x_9, x_10, x_11, x_12, x_13, x_172);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_20 = x_175;
x_21 = x_176;
goto block_27;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_162);
lean_dec(x_127);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_177 = lean_ctor_get(x_163, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_163, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_179 = x_163;
} else {
 lean_dec_ref(x_163);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_127);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_181 = lean_ctor_get(x_158, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_158, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_183 = x_158;
} else {
 lean_dec_ref(x_158);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_185 = lean_ctor_get(x_49, 0);
x_186 = lean_ctor_get(x_49, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_49);
x_187 = lean_ctor_get(x_30, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_30, 1);
lean_inc(x_188);
lean_dec(x_30);
x_189 = lean_ctor_get(x_50, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_50, 1);
lean_inc(x_190);
x_191 = lean_ctor_get(x_50, 2);
lean_inc(x_191);
x_192 = lean_nat_dec_lt(x_190, x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_187);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_185);
lean_ctor_set(x_193, 1, x_186);
lean_ctor_set(x_28, 1, x_193);
lean_ctor_set(x_28, 0, x_188);
x_194 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_194, 0, x_8);
x_20 = x_194;
x_21 = x_14;
goto block_27;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
lean_free_object(x_8);
lean_free_object(x_28);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 x_195 = x_50;
} else {
 lean_dec_ref(x_50);
 x_195 = lean_box(0);
}
x_196 = lean_array_fget(x_189, x_190);
x_197 = lean_nat_add(x_190, x_18);
lean_dec(x_190);
if (lean_is_scalar(x_195)) {
 x_198 = lean_alloc_ctor(0, 3, 0);
} else {
 x_198 = x_195;
}
lean_ctor_set(x_198, 0, x_189);
lean_ctor_set(x_198, 1, x_197);
lean_ctor_set(x_198, 2, x_191);
x_199 = lean_nat_dec_lt(x_5, x_2);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_inc(x_3);
x_200 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_201 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_187, x_196, x_200, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = lean_ctor_get(x_202, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_dec(x_202);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_186);
x_206 = l_Lean_Compiler_LCNF_compatibleTypes(x_204, x_186, x_10, x_11, x_12, x_13, x_203);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; uint8_t x_208; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_unbox(x_207);
lean_dec(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_186);
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
lean_dec(x_206);
x_210 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_211 = lean_box(0);
x_212 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_205, x_188, x_198, x_185, x_210, x_211, x_9, x_10, x_11, x_12, x_13, x_209);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_20 = x_213;
x_21 = x_214;
goto block_27;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_215 = lean_ctor_get(x_206, 1);
lean_inc(x_215);
lean_dec(x_206);
x_216 = lean_box(0);
x_217 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_205, x_188, x_198, x_185, x_186, x_216, x_9, x_10, x_11, x_12, x_13, x_215);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_20 = x_218;
x_21 = x_219;
goto block_27;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_205);
lean_dec(x_198);
lean_dec(x_188);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_220 = lean_ctor_get(x_206, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_206, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_222 = x_206;
} else {
 lean_dec_ref(x_206);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_221);
return x_223;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_198);
lean_dec(x_188);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_224 = lean_ctor_get(x_201, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_201, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_226 = x_201;
} else {
 lean_dec_ref(x_201);
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
lean_object* x_228; lean_object* x_229; 
x_228 = lean_array_fget(x_1, x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_229 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_187, x_196, x_228, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_ctor_get(x_230, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_233);
lean_dec(x_230);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_186);
x_234 = l_Lean_Compiler_LCNF_compatibleTypes(x_232, x_186, x_10, x_11, x_12, x_13, x_231);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; uint8_t x_236; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_unbox(x_235);
lean_dec(x_235);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_186);
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
lean_dec(x_234);
x_238 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_239 = lean_box(0);
x_240 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_233, x_188, x_198, x_185, x_238, x_239, x_9, x_10, x_11, x_12, x_13, x_237);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_20 = x_241;
x_21 = x_242;
goto block_27;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_243 = lean_ctor_get(x_234, 1);
lean_inc(x_243);
lean_dec(x_234);
x_244 = lean_box(0);
x_245 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_233, x_188, x_198, x_185, x_186, x_244, x_9, x_10, x_11, x_12, x_13, x_243);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_20 = x_246;
x_21 = x_247;
goto block_27;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_233);
lean_dec(x_198);
lean_dec(x_188);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_248 = lean_ctor_get(x_234, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_234, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_250 = x_234;
} else {
 lean_dec_ref(x_234);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_198);
lean_dec(x_188);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_252 = lean_ctor_get(x_229, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_229, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_254 = x_229;
} else {
 lean_dec_ref(x_229);
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
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_256 = lean_ctor_get(x_28, 1);
x_257 = lean_ctor_get(x_8, 0);
lean_inc(x_257);
lean_dec(x_8);
x_258 = lean_ctor_get(x_256, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_256, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_260 = x_256;
} else {
 lean_dec_ref(x_256);
 x_260 = lean_box(0);
}
x_261 = lean_ctor_get(x_30, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_30, 1);
lean_inc(x_262);
lean_dec(x_30);
x_263 = lean_ctor_get(x_257, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_257, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_257, 2);
lean_inc(x_265);
x_266 = lean_nat_dec_lt(x_264, x_265);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_261);
if (lean_is_scalar(x_260)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_260;
}
lean_ctor_set(x_267, 0, x_258);
lean_ctor_set(x_267, 1, x_259);
lean_ctor_set(x_28, 1, x_267);
lean_ctor_set(x_28, 0, x_262);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_257);
lean_ctor_set(x_268, 1, x_28);
x_269 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_269, 0, x_268);
x_20 = x_269;
x_21 = x_14;
goto block_27;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
lean_dec(x_260);
lean_free_object(x_28);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 lean_ctor_release(x_257, 2);
 x_270 = x_257;
} else {
 lean_dec_ref(x_257);
 x_270 = lean_box(0);
}
x_271 = lean_array_fget(x_263, x_264);
x_272 = lean_nat_add(x_264, x_18);
lean_dec(x_264);
if (lean_is_scalar(x_270)) {
 x_273 = lean_alloc_ctor(0, 3, 0);
} else {
 x_273 = x_270;
}
lean_ctor_set(x_273, 0, x_263);
lean_ctor_set(x_273, 1, x_272);
lean_ctor_set(x_273, 2, x_265);
x_274 = lean_nat_dec_lt(x_5, x_2);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; 
lean_inc(x_3);
x_275 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_276 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_261, x_271, x_275, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
x_279 = lean_ctor_get(x_277, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_277, 1);
lean_inc(x_280);
lean_dec(x_277);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_259);
x_281 = l_Lean_Compiler_LCNF_compatibleTypes(x_279, x_259, x_10, x_11, x_12, x_13, x_278);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; uint8_t x_283; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_unbox(x_282);
lean_dec(x_282);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_259);
x_284 = lean_ctor_get(x_281, 1);
lean_inc(x_284);
lean_dec(x_281);
x_285 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_286 = lean_box(0);
x_287 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_280, x_262, x_273, x_258, x_285, x_286, x_9, x_10, x_11, x_12, x_13, x_284);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
x_20 = x_288;
x_21 = x_289;
goto block_27;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_290 = lean_ctor_get(x_281, 1);
lean_inc(x_290);
lean_dec(x_281);
x_291 = lean_box(0);
x_292 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_280, x_262, x_273, x_258, x_259, x_291, x_9, x_10, x_11, x_12, x_13, x_290);
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
x_20 = x_293;
x_21 = x_294;
goto block_27;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_280);
lean_dec(x_273);
lean_dec(x_262);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_295 = lean_ctor_get(x_281, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_281, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_297 = x_281;
} else {
 lean_dec_ref(x_281);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(1, 2, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_295);
lean_ctor_set(x_298, 1, x_296);
return x_298;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_273);
lean_dec(x_262);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_299 = lean_ctor_get(x_276, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_276, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_301 = x_276;
} else {
 lean_dec_ref(x_276);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_299);
lean_ctor_set(x_302, 1, x_300);
return x_302;
}
}
else
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_array_fget(x_1, x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_304 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_261, x_271, x_303, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = lean_ctor_get(x_305, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_305, 1);
lean_inc(x_308);
lean_dec(x_305);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_259);
x_309 = l_Lean_Compiler_LCNF_compatibleTypes(x_307, x_259, x_10, x_11, x_12, x_13, x_306);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; uint8_t x_311; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_unbox(x_310);
lean_dec(x_310);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_259);
x_312 = lean_ctor_get(x_309, 1);
lean_inc(x_312);
lean_dec(x_309);
x_313 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_314 = lean_box(0);
x_315 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_308, x_262, x_273, x_258, x_313, x_314, x_9, x_10, x_11, x_12, x_13, x_312);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_20 = x_316;
x_21 = x_317;
goto block_27;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_318 = lean_ctor_get(x_309, 1);
lean_inc(x_318);
lean_dec(x_309);
x_319 = lean_box(0);
x_320 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_308, x_262, x_273, x_258, x_259, x_319, x_9, x_10, x_11, x_12, x_13, x_318);
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
x_20 = x_321;
x_21 = x_322;
goto block_27;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_308);
lean_dec(x_273);
lean_dec(x_262);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_323 = lean_ctor_get(x_309, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_309, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_325 = x_309;
} else {
 lean_dec_ref(x_309);
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
lean_dec(x_273);
lean_dec(x_262);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_327 = lean_ctor_get(x_304, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_304, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_329 = x_304;
} else {
 lean_dec_ref(x_304);
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
}
}
}
}
else
{
lean_object* x_331; lean_object* x_332; 
x_331 = lean_ctor_get(x_28, 1);
x_332 = lean_ctor_get(x_28, 0);
lean_inc(x_331);
lean_inc(x_332);
lean_dec(x_28);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_333 = lean_ctor_get(x_8, 0);
lean_inc(x_333);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_334 = x_8;
} else {
 lean_dec_ref(x_8);
 x_334 = lean_box(0);
}
x_335 = lean_ctor_get(x_331, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_331, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_337 = x_331;
} else {
 lean_dec_ref(x_331);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(0, 2, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_336);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_332);
lean_ctor_set(x_339, 1, x_338);
if (lean_is_scalar(x_334)) {
 x_340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_340 = x_334;
}
lean_ctor_set(x_340, 0, x_333);
lean_ctor_set(x_340, 1, x_339);
x_341 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_341, 0, x_340);
x_20 = x_341;
x_21 = x_14;
goto block_27;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; 
x_342 = lean_ctor_get(x_8, 0);
lean_inc(x_342);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_343 = x_8;
} else {
 lean_dec_ref(x_8);
 x_343 = lean_box(0);
}
x_344 = lean_ctor_get(x_331, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_331, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_346 = x_331;
} else {
 lean_dec_ref(x_331);
 x_346 = lean_box(0);
}
x_347 = lean_ctor_get(x_332, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_332, 1);
lean_inc(x_348);
lean_dec(x_332);
x_349 = lean_ctor_get(x_342, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_342, 1);
lean_inc(x_350);
x_351 = lean_ctor_get(x_342, 2);
lean_inc(x_351);
x_352 = lean_nat_dec_lt(x_350, x_351);
if (x_352 == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_347);
if (lean_is_scalar(x_346)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_346;
}
lean_ctor_set(x_353, 0, x_344);
lean_ctor_set(x_353, 1, x_345);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_348);
lean_ctor_set(x_354, 1, x_353);
if (lean_is_scalar(x_343)) {
 x_355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_355 = x_343;
}
lean_ctor_set(x_355, 0, x_342);
lean_ctor_set(x_355, 1, x_354);
x_356 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_356, 0, x_355);
x_20 = x_356;
x_21 = x_14;
goto block_27;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; uint8_t x_361; 
lean_dec(x_346);
lean_dec(x_343);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 lean_ctor_release(x_342, 2);
 x_357 = x_342;
} else {
 lean_dec_ref(x_342);
 x_357 = lean_box(0);
}
x_358 = lean_array_fget(x_349, x_350);
x_359 = lean_nat_add(x_350, x_18);
lean_dec(x_350);
if (lean_is_scalar(x_357)) {
 x_360 = lean_alloc_ctor(0, 3, 0);
} else {
 x_360 = x_357;
}
lean_ctor_set(x_360, 0, x_349);
lean_ctor_set(x_360, 1, x_359);
lean_ctor_set(x_360, 2, x_351);
x_361 = lean_nat_dec_lt(x_5, x_2);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; 
lean_inc(x_3);
x_362 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_363 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_347, x_358, x_362, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
lean_dec(x_363);
x_366 = lean_ctor_get(x_364, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_364, 1);
lean_inc(x_367);
lean_dec(x_364);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_345);
x_368 = l_Lean_Compiler_LCNF_compatibleTypes(x_366, x_345, x_10, x_11, x_12, x_13, x_365);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; uint8_t x_370; 
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_unbox(x_369);
lean_dec(x_369);
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_345);
x_371 = lean_ctor_get(x_368, 1);
lean_inc(x_371);
lean_dec(x_368);
x_372 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_373 = lean_box(0);
x_374 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_367, x_348, x_360, x_344, x_372, x_373, x_9, x_10, x_11, x_12, x_13, x_371);
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec(x_374);
x_20 = x_375;
x_21 = x_376;
goto block_27;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_377 = lean_ctor_get(x_368, 1);
lean_inc(x_377);
lean_dec(x_368);
x_378 = lean_box(0);
x_379 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_367, x_348, x_360, x_344, x_345, x_378, x_9, x_10, x_11, x_12, x_13, x_377);
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
lean_dec(x_379);
x_20 = x_380;
x_21 = x_381;
goto block_27;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_367);
lean_dec(x_360);
lean_dec(x_348);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_382 = lean_ctor_get(x_368, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_368, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_384 = x_368;
} else {
 lean_dec_ref(x_368);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_384)) {
 x_385 = lean_alloc_ctor(1, 2, 0);
} else {
 x_385 = x_384;
}
lean_ctor_set(x_385, 0, x_382);
lean_ctor_set(x_385, 1, x_383);
return x_385;
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_360);
lean_dec(x_348);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_386 = lean_ctor_get(x_363, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_363, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_388 = x_363;
} else {
 lean_dec_ref(x_363);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(1, 2, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_387);
return x_389;
}
}
else
{
lean_object* x_390; lean_object* x_391; 
x_390 = lean_array_fget(x_1, x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_391 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_347, x_358, x_390, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
x_394 = lean_ctor_get(x_392, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_392, 1);
lean_inc(x_395);
lean_dec(x_392);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_345);
x_396 = l_Lean_Compiler_LCNF_compatibleTypes(x_394, x_345, x_10, x_11, x_12, x_13, x_393);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; uint8_t x_398; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_unbox(x_397);
lean_dec(x_397);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_dec(x_345);
x_399 = lean_ctor_get(x_396, 1);
lean_inc(x_399);
lean_dec(x_396);
x_400 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_401 = lean_box(0);
x_402 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_395, x_348, x_360, x_344, x_400, x_401, x_9, x_10, x_11, x_12, x_13, x_399);
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
lean_dec(x_402);
x_20 = x_403;
x_21 = x_404;
goto block_27;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_405 = lean_ctor_get(x_396, 1);
lean_inc(x_405);
lean_dec(x_396);
x_406 = lean_box(0);
x_407 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_395, x_348, x_360, x_344, x_345, x_406, x_9, x_10, x_11, x_12, x_13, x_405);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_20 = x_408;
x_21 = x_409;
goto block_27;
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_dec(x_395);
lean_dec(x_360);
lean_dec(x_348);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_410 = lean_ctor_get(x_396, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_396, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_412 = x_396;
} else {
 lean_dec_ref(x_396);
 x_412 = lean_box(0);
}
if (lean_is_scalar(x_412)) {
 x_413 = lean_alloc_ctor(1, 2, 0);
} else {
 x_413 = x_412;
}
lean_ctor_set(x_413, 0, x_410);
lean_ctor_set(x_413, 1, x_411);
return x_413;
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_360);
lean_dec(x_348);
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_414 = lean_ctor_get(x_391, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_391, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_416 = x_391;
} else {
 lean_dec_ref(x_391);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(1, 2, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_414);
lean_ctor_set(x_417, 1, x_415);
return x_417;
}
}
}
}
}
block_27:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_19;
x_5 = x_25;
x_8 = x_24;
x_14 = x_21;
goto _start;
}
}
}
else
{
lean_object* x_418; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_418, 0, x_8);
lean_ctor_set(x_418, 1, x_14);
return x_418;
}
}
else
{
lean_object* x_419; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_419 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_419, 0, x_8);
lean_ctor_set(x_419, 1, x_14);
return x_419;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_27; uint8_t x_28; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_3, x_17);
lean_dec(x_3);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_27, 1);
x_32 = lean_ctor_get(x_7, 1);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_7);
x_19 = x_34;
x_20 = x_13;
goto block_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_27, 1, x_37);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_7);
x_19 = x_38;
x_20 = x_13;
goto block_26;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_27, 1);
x_40 = lean_ctor_get(x_7, 0);
lean_inc(x_40);
lean_dec(x_7);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_43 = x_39;
} else {
 lean_dec_ref(x_39);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_27, 1, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_27);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_19 = x_46;
x_20 = x_13;
goto block_26;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_7);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_27, 1);
x_49 = lean_ctor_get(x_7, 0);
x_50 = lean_ctor_get(x_7, 1);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
x_54 = lean_ctor_get(x_29, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_29, 1);
lean_inc(x_55);
lean_dec(x_29);
x_56 = lean_ctor_get(x_49, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_49, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_49, 2);
lean_inc(x_58);
x_59 = lean_nat_dec_lt(x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_54);
lean_ctor_set(x_27, 0, x_55);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_7);
x_19 = x_60;
x_20 = x_13;
goto block_26;
}
else
{
uint8_t x_61; 
lean_free_object(x_48);
lean_free_object(x_7);
lean_free_object(x_27);
x_61 = !lean_is_exclusive(x_49);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_62 = lean_ctor_get(x_49, 2);
lean_dec(x_62);
x_63 = lean_ctor_get(x_49, 1);
lean_dec(x_63);
x_64 = lean_ctor_get(x_49, 0);
lean_dec(x_64);
x_65 = lean_array_fget(x_56, x_57);
x_66 = lean_nat_add(x_57, x_17);
lean_dec(x_57);
lean_ctor_set(x_49, 1, x_66);
x_67 = lean_nat_dec_lt(x_4, x_2);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_69 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_68);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_70 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_54, x_65, x_69, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_53);
x_75 = l_Lean_Compiler_LCNF_compatibleTypes(x_73, x_53, x_9, x_10, x_11, x_12, x_72);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_53);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_80 = lean_box(0);
x_81 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_74, x_55, x_49, x_52, x_79, x_80, x_8, x_9, x_10, x_11, x_12, x_78);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_19 = x_82;
x_20 = x_83;
goto block_26;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_75, 1);
lean_inc(x_84);
lean_dec(x_75);
x_85 = lean_box(0);
x_86 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_74, x_55, x_49, x_52, x_53, x_85, x_8, x_9, x_10, x_11, x_12, x_84);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_19 = x_87;
x_20 = x_88;
goto block_26;
}
}
else
{
uint8_t x_89; 
lean_dec(x_74);
lean_dec(x_49);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_89 = !lean_is_exclusive(x_75);
if (x_89 == 0)
{
return x_75;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_75, 0);
x_91 = lean_ctor_get(x_75, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_75);
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
lean_dec(x_49);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_93 = !lean_is_exclusive(x_70);
if (x_93 == 0)
{
return x_70;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_70, 0);
x_95 = lean_ctor_get(x_70, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_70);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_array_fget(x_1, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_98 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_54, x_65, x_97, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_53);
x_103 = l_Lean_Compiler_LCNF_compatibleTypes(x_101, x_53, x_9, x_10, x_11, x_12, x_100);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_53);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_108 = lean_box(0);
x_109 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_102, x_55, x_49, x_52, x_107, x_108, x_8, x_9, x_10, x_11, x_12, x_106);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_19 = x_110;
x_20 = x_111;
goto block_26;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_103, 1);
lean_inc(x_112);
lean_dec(x_103);
x_113 = lean_box(0);
x_114 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_102, x_55, x_49, x_52, x_53, x_113, x_8, x_9, x_10, x_11, x_12, x_112);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_19 = x_115;
x_20 = x_116;
goto block_26;
}
}
else
{
uint8_t x_117; 
lean_dec(x_102);
lean_dec(x_49);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_117 = !lean_is_exclusive(x_103);
if (x_117 == 0)
{
return x_103;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_103, 0);
x_119 = lean_ctor_get(x_103, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_103);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_49);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_121 = !lean_is_exclusive(x_98);
if (x_121 == 0)
{
return x_98;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_98, 0);
x_123 = lean_ctor_get(x_98, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_98);
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
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_49);
x_125 = lean_array_fget(x_56, x_57);
x_126 = lean_nat_add(x_57, x_17);
lean_dec(x_57);
x_127 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_127, 0, x_56);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_127, 2, x_58);
x_128 = lean_nat_dec_lt(x_4, x_2);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_130 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_129);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_131 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_54, x_125, x_130, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_dec(x_132);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_53);
x_136 = l_Lean_Compiler_LCNF_compatibleTypes(x_134, x_53, x_9, x_10, x_11, x_12, x_133);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_53);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
x_140 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_141 = lean_box(0);
x_142 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_135, x_55, x_127, x_52, x_140, x_141, x_8, x_9, x_10, x_11, x_12, x_139);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_19 = x_143;
x_20 = x_144;
goto block_26;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_136, 1);
lean_inc(x_145);
lean_dec(x_136);
x_146 = lean_box(0);
x_147 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_135, x_55, x_127, x_52, x_53, x_146, x_8, x_9, x_10, x_11, x_12, x_145);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_19 = x_148;
x_20 = x_149;
goto block_26;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_135);
lean_dec(x_127);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_150 = lean_ctor_get(x_136, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_136, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_152 = x_136;
} else {
 lean_dec_ref(x_136);
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
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_127);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_154 = lean_ctor_get(x_131, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_131, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_156 = x_131;
} else {
 lean_dec_ref(x_131);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_array_fget(x_1, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_159 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_54, x_125, x_158, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
lean_dec(x_160);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_53);
x_164 = l_Lean_Compiler_LCNF_compatibleTypes(x_162, x_53, x_9, x_10, x_11, x_12, x_161);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; uint8_t x_166; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_unbox(x_165);
lean_dec(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_53);
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_167);
lean_dec(x_164);
x_168 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_169 = lean_box(0);
x_170 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_163, x_55, x_127, x_52, x_168, x_169, x_8, x_9, x_10, x_11, x_12, x_167);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_19 = x_171;
x_20 = x_172;
goto block_26;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_173 = lean_ctor_get(x_164, 1);
lean_inc(x_173);
lean_dec(x_164);
x_174 = lean_box(0);
x_175 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_163, x_55, x_127, x_52, x_53, x_174, x_8, x_9, x_10, x_11, x_12, x_173);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_19 = x_176;
x_20 = x_177;
goto block_26;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_163);
lean_dec(x_127);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_178 = lean_ctor_get(x_164, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_164, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_180 = x_164;
} else {
 lean_dec_ref(x_164);
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
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_127);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_182 = lean_ctor_get(x_159, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_159, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_184 = x_159;
} else {
 lean_dec_ref(x_159);
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
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_186 = lean_ctor_get(x_48, 0);
x_187 = lean_ctor_get(x_48, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_48);
x_188 = lean_ctor_get(x_29, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_29, 1);
lean_inc(x_189);
lean_dec(x_29);
x_190 = lean_ctor_get(x_49, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_49, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_49, 2);
lean_inc(x_192);
x_193 = lean_nat_dec_lt(x_191, x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_188);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_186);
lean_ctor_set(x_194, 1, x_187);
lean_ctor_set(x_27, 1, x_194);
lean_ctor_set(x_27, 0, x_189);
x_195 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_195, 0, x_7);
x_19 = x_195;
x_20 = x_13;
goto block_26;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
lean_free_object(x_7);
lean_free_object(x_27);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 lean_ctor_release(x_49, 2);
 x_196 = x_49;
} else {
 lean_dec_ref(x_49);
 x_196 = lean_box(0);
}
x_197 = lean_array_fget(x_190, x_191);
x_198 = lean_nat_add(x_191, x_17);
lean_dec(x_191);
if (lean_is_scalar(x_196)) {
 x_199 = lean_alloc_ctor(0, 3, 0);
} else {
 x_199 = x_196;
}
lean_ctor_set(x_199, 0, x_190);
lean_ctor_set(x_199, 1, x_198);
lean_ctor_set(x_199, 2, x_192);
x_200 = lean_nat_dec_lt(x_4, x_2);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_202 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_201);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_203 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_188, x_197, x_202, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = lean_ctor_get(x_204, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_204, 1);
lean_inc(x_207);
lean_dec(x_204);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_187);
x_208 = l_Lean_Compiler_LCNF_compatibleTypes(x_206, x_187, x_9, x_10, x_11, x_12, x_205);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; uint8_t x_210; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_unbox(x_209);
lean_dec(x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_187);
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
lean_dec(x_208);
x_212 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_213 = lean_box(0);
x_214 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_207, x_189, x_199, x_186, x_212, x_213, x_8, x_9, x_10, x_11, x_12, x_211);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_19 = x_215;
x_20 = x_216;
goto block_26;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_217 = lean_ctor_get(x_208, 1);
lean_inc(x_217);
lean_dec(x_208);
x_218 = lean_box(0);
x_219 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_207, x_189, x_199, x_186, x_187, x_218, x_8, x_9, x_10, x_11, x_12, x_217);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_19 = x_220;
x_20 = x_221;
goto block_26;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_207);
lean_dec(x_199);
lean_dec(x_189);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_222 = lean_ctor_get(x_208, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_208, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_224 = x_208;
} else {
 lean_dec_ref(x_208);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_223);
return x_225;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_199);
lean_dec(x_189);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_226 = lean_ctor_get(x_203, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_203, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_228 = x_203;
} else {
 lean_dec_ref(x_203);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_array_fget(x_1, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_231 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_188, x_197, x_230, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_ctor_get(x_232, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_232, 1);
lean_inc(x_235);
lean_dec(x_232);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_187);
x_236 = l_Lean_Compiler_LCNF_compatibleTypes(x_234, x_187, x_9, x_10, x_11, x_12, x_233);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; uint8_t x_238; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_unbox(x_237);
lean_dec(x_237);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_187);
x_239 = lean_ctor_get(x_236, 1);
lean_inc(x_239);
lean_dec(x_236);
x_240 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_241 = lean_box(0);
x_242 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_235, x_189, x_199, x_186, x_240, x_241, x_8, x_9, x_10, x_11, x_12, x_239);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_19 = x_243;
x_20 = x_244;
goto block_26;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_245 = lean_ctor_get(x_236, 1);
lean_inc(x_245);
lean_dec(x_236);
x_246 = lean_box(0);
x_247 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_235, x_189, x_199, x_186, x_187, x_246, x_8, x_9, x_10, x_11, x_12, x_245);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_19 = x_248;
x_20 = x_249;
goto block_26;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_235);
lean_dec(x_199);
lean_dec(x_189);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_250 = lean_ctor_get(x_236, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_236, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_252 = x_236;
} else {
 lean_dec_ref(x_236);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_251);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_199);
lean_dec(x_189);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_254 = lean_ctor_get(x_231, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_231, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_256 = x_231;
} else {
 lean_dec_ref(x_231);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
}
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_258 = lean_ctor_get(x_27, 1);
x_259 = lean_ctor_get(x_7, 0);
lean_inc(x_259);
lean_dec(x_7);
x_260 = lean_ctor_get(x_258, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_262 = x_258;
} else {
 lean_dec_ref(x_258);
 x_262 = lean_box(0);
}
x_263 = lean_ctor_get(x_29, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_29, 1);
lean_inc(x_264);
lean_dec(x_29);
x_265 = lean_ctor_get(x_259, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_259, 1);
lean_inc(x_266);
x_267 = lean_ctor_get(x_259, 2);
lean_inc(x_267);
x_268 = lean_nat_dec_lt(x_266, x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_263);
if (lean_is_scalar(x_262)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_262;
}
lean_ctor_set(x_269, 0, x_260);
lean_ctor_set(x_269, 1, x_261);
lean_ctor_set(x_27, 1, x_269);
lean_ctor_set(x_27, 0, x_264);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_259);
lean_ctor_set(x_270, 1, x_27);
x_271 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_271, 0, x_270);
x_19 = x_271;
x_20 = x_13;
goto block_26;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
lean_dec(x_262);
lean_free_object(x_27);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 lean_ctor_release(x_259, 2);
 x_272 = x_259;
} else {
 lean_dec_ref(x_259);
 x_272 = lean_box(0);
}
x_273 = lean_array_fget(x_265, x_266);
x_274 = lean_nat_add(x_266, x_17);
lean_dec(x_266);
if (lean_is_scalar(x_272)) {
 x_275 = lean_alloc_ctor(0, 3, 0);
} else {
 x_275 = x_272;
}
lean_ctor_set(x_275, 0, x_265);
lean_ctor_set(x_275, 1, x_274);
lean_ctor_set(x_275, 2, x_267);
x_276 = lean_nat_dec_lt(x_4, x_2);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_278 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_277);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_279 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_263, x_273, x_278, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = lean_ctor_get(x_280, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
lean_dec(x_280);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_261);
x_284 = l_Lean_Compiler_LCNF_compatibleTypes(x_282, x_261, x_9, x_10, x_11, x_12, x_281);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; uint8_t x_286; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_unbox(x_285);
lean_dec(x_285);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_261);
x_287 = lean_ctor_get(x_284, 1);
lean_inc(x_287);
lean_dec(x_284);
x_288 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_289 = lean_box(0);
x_290 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_283, x_264, x_275, x_260, x_288, x_289, x_8, x_9, x_10, x_11, x_12, x_287);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_19 = x_291;
x_20 = x_292;
goto block_26;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_ctor_get(x_284, 1);
lean_inc(x_293);
lean_dec(x_284);
x_294 = lean_box(0);
x_295 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_283, x_264, x_275, x_260, x_261, x_294, x_8, x_9, x_10, x_11, x_12, x_293);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_19 = x_296;
x_20 = x_297;
goto block_26;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_283);
lean_dec(x_275);
lean_dec(x_264);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_298 = lean_ctor_get(x_284, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_284, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_300 = x_284;
} else {
 lean_dec_ref(x_284);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_299);
return x_301;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_275);
lean_dec(x_264);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_302 = lean_ctor_get(x_279, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_279, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_304 = x_279;
} else {
 lean_dec_ref(x_279);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_302);
lean_ctor_set(x_305, 1, x_303);
return x_305;
}
}
else
{
lean_object* x_306; lean_object* x_307; 
x_306 = lean_array_fget(x_1, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_307 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_263, x_273, x_306, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = lean_ctor_get(x_308, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_308, 1);
lean_inc(x_311);
lean_dec(x_308);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_261);
x_312 = l_Lean_Compiler_LCNF_compatibleTypes(x_310, x_261, x_9, x_10, x_11, x_12, x_309);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; uint8_t x_314; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_unbox(x_313);
lean_dec(x_313);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_261);
x_315 = lean_ctor_get(x_312, 1);
lean_inc(x_315);
lean_dec(x_312);
x_316 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_317 = lean_box(0);
x_318 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_311, x_264, x_275, x_260, x_316, x_317, x_8, x_9, x_10, x_11, x_12, x_315);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
x_19 = x_319;
x_20 = x_320;
goto block_26;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_321 = lean_ctor_get(x_312, 1);
lean_inc(x_321);
lean_dec(x_312);
x_322 = lean_box(0);
x_323 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_311, x_264, x_275, x_260, x_261, x_322, x_8, x_9, x_10, x_11, x_12, x_321);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_19 = x_324;
x_20 = x_325;
goto block_26;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_311);
lean_dec(x_275);
lean_dec(x_264);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_326 = lean_ctor_get(x_312, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_312, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_328 = x_312;
} else {
 lean_dec_ref(x_312);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_326);
lean_ctor_set(x_329, 1, x_327);
return x_329;
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_275);
lean_dec(x_264);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_330 = lean_ctor_get(x_307, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_307, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_332 = x_307;
} else {
 lean_dec_ref(x_307);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(1, 2, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_330);
lean_ctor_set(x_333, 1, x_331);
return x_333;
}
}
}
}
}
}
else
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_ctor_get(x_27, 1);
x_335 = lean_ctor_get(x_27, 0);
lean_inc(x_334);
lean_inc(x_335);
lean_dec(x_27);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_336 = lean_ctor_get(x_7, 0);
lean_inc(x_336);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_337 = x_7;
} else {
 lean_dec_ref(x_7);
 x_337 = lean_box(0);
}
x_338 = lean_ctor_get(x_334, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_334, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_340 = x_334;
} else {
 lean_dec_ref(x_334);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_339);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_335);
lean_ctor_set(x_342, 1, x_341);
if (lean_is_scalar(x_337)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_337;
}
lean_ctor_set(x_343, 0, x_336);
lean_ctor_set(x_343, 1, x_342);
x_344 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_344, 0, x_343);
x_19 = x_344;
x_20 = x_13;
goto block_26;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; 
x_345 = lean_ctor_get(x_7, 0);
lean_inc(x_345);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_346 = x_7;
} else {
 lean_dec_ref(x_7);
 x_346 = lean_box(0);
}
x_347 = lean_ctor_get(x_334, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_334, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_349 = x_334;
} else {
 lean_dec_ref(x_334);
 x_349 = lean_box(0);
}
x_350 = lean_ctor_get(x_335, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_335, 1);
lean_inc(x_351);
lean_dec(x_335);
x_352 = lean_ctor_get(x_345, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_345, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_345, 2);
lean_inc(x_354);
x_355 = lean_nat_dec_lt(x_353, x_354);
if (x_355 == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_350);
if (lean_is_scalar(x_349)) {
 x_356 = lean_alloc_ctor(0, 2, 0);
} else {
 x_356 = x_349;
}
lean_ctor_set(x_356, 0, x_347);
lean_ctor_set(x_356, 1, x_348);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_351);
lean_ctor_set(x_357, 1, x_356);
if (lean_is_scalar(x_346)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_346;
}
lean_ctor_set(x_358, 0, x_345);
lean_ctor_set(x_358, 1, x_357);
x_359 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_359, 0, x_358);
x_19 = x_359;
x_20 = x_13;
goto block_26;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; 
lean_dec(x_349);
lean_dec(x_346);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 lean_ctor_release(x_345, 2);
 x_360 = x_345;
} else {
 lean_dec_ref(x_345);
 x_360 = lean_box(0);
}
x_361 = lean_array_fget(x_352, x_353);
x_362 = lean_nat_add(x_353, x_17);
lean_dec(x_353);
if (lean_is_scalar(x_360)) {
 x_363 = lean_alloc_ctor(0, 3, 0);
} else {
 x_363 = x_360;
}
lean_ctor_set(x_363, 0, x_352);
lean_ctor_set(x_363, 1, x_362);
lean_ctor_set(x_363, 2, x_354);
x_364 = lean_nat_dec_lt(x_4, x_2);
if (x_364 == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_366 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_365);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_367 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_350, x_361, x_366, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec(x_367);
x_370 = lean_ctor_get(x_368, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_368, 1);
lean_inc(x_371);
lean_dec(x_368);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_348);
x_372 = l_Lean_Compiler_LCNF_compatibleTypes(x_370, x_348, x_9, x_10, x_11, x_12, x_369);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; uint8_t x_374; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_unbox(x_373);
lean_dec(x_373);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_348);
x_375 = lean_ctor_get(x_372, 1);
lean_inc(x_375);
lean_dec(x_372);
x_376 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_377 = lean_box(0);
x_378 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_371, x_351, x_363, x_347, x_376, x_377, x_8, x_9, x_10, x_11, x_12, x_375);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_19 = x_379;
x_20 = x_380;
goto block_26;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_381 = lean_ctor_get(x_372, 1);
lean_inc(x_381);
lean_dec(x_372);
x_382 = lean_box(0);
x_383 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_371, x_351, x_363, x_347, x_348, x_382, x_8, x_9, x_10, x_11, x_12, x_381);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
lean_dec(x_383);
x_19 = x_384;
x_20 = x_385;
goto block_26;
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_371);
lean_dec(x_363);
lean_dec(x_351);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_386 = lean_ctor_get(x_372, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_372, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_388 = x_372;
} else {
 lean_dec_ref(x_372);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(1, 2, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_387);
return x_389;
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_363);
lean_dec(x_351);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_390 = lean_ctor_get(x_367, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_367, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_392 = x_367;
} else {
 lean_dec_ref(x_367);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 2, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_390);
lean_ctor_set(x_393, 1, x_391);
return x_393;
}
}
else
{
lean_object* x_394; lean_object* x_395; 
x_394 = lean_array_fget(x_1, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_395 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_350, x_361, x_394, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
x_398 = lean_ctor_get(x_396, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_396, 1);
lean_inc(x_399);
lean_dec(x_396);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_348);
x_400 = l_Lean_Compiler_LCNF_compatibleTypes(x_398, x_348, x_9, x_10, x_11, x_12, x_397);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; uint8_t x_402; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_unbox(x_401);
lean_dec(x_401);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec(x_348);
x_403 = lean_ctor_get(x_400, 1);
lean_inc(x_403);
lean_dec(x_400);
x_404 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_405 = lean_box(0);
x_406 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_399, x_351, x_363, x_347, x_404, x_405, x_8, x_9, x_10, x_11, x_12, x_403);
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
lean_dec(x_406);
x_19 = x_407;
x_20 = x_408;
goto block_26;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_409 = lean_ctor_get(x_400, 1);
lean_inc(x_409);
lean_dec(x_400);
x_410 = lean_box(0);
x_411 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_399, x_351, x_363, x_347, x_348, x_410, x_8, x_9, x_10, x_11, x_12, x_409);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_19 = x_412;
x_20 = x_413;
goto block_26;
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_399);
lean_dec(x_363);
lean_dec(x_351);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_414 = lean_ctor_get(x_400, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_400, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 x_416 = x_400;
} else {
 lean_dec_ref(x_400);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(1, 2, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_414);
lean_ctor_set(x_417, 1, x_415);
return x_417;
}
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_363);
lean_dec(x_351);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_418 = lean_ctor_get(x_395, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_395, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 x_420 = x_395;
} else {
 lean_dec_ref(x_395);
 x_420 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_421 = x_420;
}
lean_ctor_set(x_421, 0, x_418);
lean_ctor_set(x_421, 1, x_419);
return x_421;
}
}
}
}
}
block_26:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_24;
x_7 = x_23;
x_13 = x_20;
goto _start;
}
}
}
else
{
lean_object* x_422; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_422, 0, x_7);
lean_ctor_set(x_422, 1, x_13);
return x_422;
}
}
else
{
lean_object* x_423; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_423 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_423, 0, x_7);
lean_ctor_set(x_423, 1, x_13);
return x_423;
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
x_3 = lean_unsigned_to_nat(531u);
x_4 = lean_unsigned_to_nat(57u);
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
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
lean_dec(x_17);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
x_20 = lean_array_get_size(x_2);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_23 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_22);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_1, 5);
lean_inc(x_31);
x_32 = lean_array_get_size(x_31);
x_33 = l_Array_toSubarray___rarg(x_31, x_15, x_32);
x_34 = lean_ctor_get(x_30, 4);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_ctor_get(x_1, 4);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_12);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_35, 2);
lean_inc(x_42);
lean_dec(x_35);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_40);
x_43 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1(x_2, x_20, x_22, x_40, x_41, x_40, x_42, x_39, x_5, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_42);
lean_dec(x_40);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = l_Lean_Expr_fvarId_x21(x_25);
lean_inc(x_49);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_18);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_51, 3, x_48);
x_52 = 0;
x_53 = l_Lean_Compiler_LCNF_mkAuxParam(x_49, x_52, x_6, x_7, x_8, x_9, x_47);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_54);
x_56 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_51);
x_57 = l_Lean_Compiler_LCNF_ToLCNF_pushElement(x_56, x_5, x_6, x_7, x_8, x_9, x_55);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_57, 1);
x_60 = lean_ctor_get(x_57, 0);
lean_dec(x_60);
x_61 = lean_ctor_get(x_54, 0);
lean_inc(x_61);
lean_dec(x_54);
x_62 = l_Lean_Expr_fvar___override(x_61);
x_63 = lean_nat_dec_eq(x_20, x_3);
lean_dec(x_20);
if (x_63 == 0)
{
lean_object* x_64; 
lean_free_object(x_57);
x_64 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_62, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_59);
return x_64;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_57, 0, x_62);
return x_57;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_57, 1);
lean_inc(x_65);
lean_dec(x_57);
x_66 = lean_ctor_get(x_54, 0);
lean_inc(x_66);
lean_dec(x_54);
x_67 = l_Lean_Expr_fvar___override(x_66);
x_68 = lean_nat_dec_eq(x_20, x_3);
lean_dec(x_20);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_67, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_65);
return x_69;
}
else
{
lean_object* x_70; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_65);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_43);
if (x_71 == 0)
{
return x_43;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_43, 0);
x_73 = lean_ctor_get(x_43, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_43);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = lean_ctor_get(x_27, 1);
lean_inc(x_75);
lean_dec(x_27);
x_76 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__2;
x_77 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_76, x_5, x_6, x_7, x_8, x_9, x_75);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_27);
if (x_78 == 0)
{
return x_27;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_27, 0);
x_80 = lean_ctor_get(x_27, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_27);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_24);
if (x_82 == 0)
{
return x_24;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_24, 0);
x_84 = lean_ctor_get(x_24, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_24);
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
x_86 = lean_array_fget(x_2, x_19);
lean_dec(x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_87 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_86, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_18);
x_90 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1(x_18, x_5, x_6, x_7, x_8, x_9, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 5)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_1, 5);
lean_inc(x_94);
x_95 = lean_array_get_size(x_94);
x_96 = l_Array_toSubarray___rarg(x_94, x_15, x_95);
x_97 = lean_ctor_get(x_93, 4);
lean_inc(x_97);
lean_dec(x_93);
x_98 = lean_ctor_get(x_1, 4);
lean_inc(x_98);
lean_dec(x_1);
x_99 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_12);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_96);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 2);
lean_inc(x_105);
lean_dec(x_98);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_103);
x_106 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__2(x_2, x_20, x_103, x_104, x_103, x_105, x_102, x_5, x_6, x_7, x_8, x_9, x_92);
lean_dec(x_105);
lean_dec(x_103);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
lean_dec(x_106);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
x_113 = l_Lean_Expr_fvarId_x21(x_88);
lean_inc(x_112);
x_114 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_114, 0, x_18);
lean_ctor_set(x_114, 1, x_112);
lean_ctor_set(x_114, 2, x_113);
lean_ctor_set(x_114, 3, x_111);
x_115 = 0;
x_116 = l_Lean_Compiler_LCNF_mkAuxParam(x_112, x_115, x_6, x_7, x_8, x_9, x_110);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_117);
x_119 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_114);
x_120 = l_Lean_Compiler_LCNF_ToLCNF_pushElement(x_119, x_5, x_6, x_7, x_8, x_9, x_118);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_122 = lean_ctor_get(x_120, 1);
x_123 = lean_ctor_get(x_120, 0);
lean_dec(x_123);
x_124 = lean_ctor_get(x_117, 0);
lean_inc(x_124);
lean_dec(x_117);
x_125 = l_Lean_Expr_fvar___override(x_124);
x_126 = lean_nat_dec_eq(x_20, x_3);
lean_dec(x_20);
if (x_126 == 0)
{
lean_object* x_127; 
lean_free_object(x_120);
x_127 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_125, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_122);
return x_127;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_120, 0, x_125);
return x_120;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_128 = lean_ctor_get(x_120, 1);
lean_inc(x_128);
lean_dec(x_120);
x_129 = lean_ctor_get(x_117, 0);
lean_inc(x_129);
lean_dec(x_117);
x_130 = l_Lean_Expr_fvar___override(x_129);
x_131 = lean_nat_dec_eq(x_20, x_3);
lean_dec(x_20);
if (x_131 == 0)
{
lean_object* x_132; 
x_132 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_130, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_128);
return x_132;
}
else
{
lean_object* x_133; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_128);
return x_133;
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_88);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_134 = !lean_is_exclusive(x_106);
if (x_134 == 0)
{
return x_106;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_106, 0);
x_136 = lean_ctor_get(x_106, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_106);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_91);
lean_dec(x_88);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_138 = lean_ctor_get(x_90, 1);
lean_inc(x_138);
lean_dec(x_90);
x_139 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__2;
x_140 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_139, x_5, x_6, x_7, x_8, x_9, x_138);
return x_140;
}
}
else
{
uint8_t x_141; 
lean_dec(x_88);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = !lean_is_exclusive(x_90);
if (x_141 == 0)
{
return x_90;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_90, 0);
x_143 = lean_ctor_get(x_90, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_90);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = !lean_is_exclusive(x_87);
if (x_145 == 0)
{
return x_87;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_87, 0);
x_147 = lean_ctor_get(x_87, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_87);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
else
{
lean_object* x_149; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_12, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_149;
}
}
else
{
uint8_t x_150; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_11);
if (x_150 == 0)
{
return x_11;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_11, 0);
x_152 = lean_ctor_get(x_11, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_11);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
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
x_12 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_1, x_15);
lean_dec(x_1);
x_17 = lean_array_get_size(x_5);
x_18 = lean_nat_dec_lt(x_2, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_16;
x_2 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_array_fget(x_5, x_2);
x_22 = lean_box(0);
x_23 = lean_array_fset(x_5, x_2, x_22);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_21, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_fset(x_23, x_2, x_25);
x_28 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_16;
x_2 = x_28;
x_5 = x_27;
x_11 = x_26;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
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
}
else
{
lean_object* x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_11);
return x_34;
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
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_11);
return x_35;
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
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_1, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_10);
x_17 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___spec__1(x_10, x_3, x_10, x_16, x_2, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get_size(x_18);
x_21 = l_Array_toSubarray___rarg(x_18, x_3, x_20);
x_22 = l_Array_ofSubarray___rarg(x_21);
x_23 = l_Lean_mkAppN(x_14, x_22);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_23, x_12, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_4);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_33 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
x_34 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_1, x_33, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_34;
}
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1___closed__1;
x_11 = lean_st_ref_get(x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_5, 2);
x_15 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_13, x_14, x_1);
lean_dec(x_13);
x_16 = lean_box(x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_ctor_get(x_5, 2);
x_20 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_17, x_19, x_1);
lean_dec(x_17);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_st_ref_get(x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_5, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
x_19 = lean_ctor_get(x_6, 2);
x_20 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__6;
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
x_22 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_2);
x_23 = lean_st_ref_take(x_7, x_16);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_27 = lean_ctor_get(x_24, 3);
x_28 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_29 = 0;
x_30 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_29);
lean_inc(x_9);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_9);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_PersistentArray_push___rarg(x_27, x_31);
lean_ctor_set(x_24, 3, x_32);
x_33 = lean_st_ref_set(x_7, x_24, x_25);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
x_42 = lean_ctor_get(x_24, 2);
x_43 = lean_ctor_get(x_24, 3);
x_44 = lean_ctor_get(x_24, 4);
x_45 = lean_ctor_get(x_24, 5);
x_46 = lean_ctor_get(x_24, 6);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_47 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_48 = 0;
x_49 = lean_alloc_ctor(12, 3, 1);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_22);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_48);
lean_inc(x_9);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_9);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_PersistentArray_push___rarg(x_43, x_50);
x_52 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_52, 0, x_40);
lean_ctor_set(x_52, 1, x_41);
lean_ctor_set(x_52, 2, x_42);
lean_ctor_set(x_52, 3, x_51);
lean_ctor_set(x_52, 4, x_44);
lean_ctor_set(x_52, 5, x_45);
lean_ctor_set(x_52, 6, x_46);
x_53 = lean_st_ref_set(x_7, x_52, x_25);
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
x_56 = lean_box(0);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_take(x_4, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_13, 5);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = l_Lean_RBNode_insert___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectExpr___spec__1(x_16, x_17, x_18);
lean_ctor_set(x_13, 5, x_19);
x_20 = lean_st_ref_set(x_4, x_13, x_14);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_apply_7(x_2, x_18, x_4, x_5, x_6, x_7, x_8, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
x_25 = lean_ctor_get(x_13, 2);
x_26 = lean_ctor_get(x_13, 3);
x_27 = lean_ctor_get(x_13, 4);
x_28 = lean_ctor_get(x_13, 5);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_box(0);
x_31 = l_Lean_RBNode_insert___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_collectExpr___spec__1(x_28, x_29, x_30);
x_32 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_26);
lean_ctor_set(x_32, 4, x_27);
lean_ctor_set(x_32, 5, x_31);
x_33 = lean_st_ref_set(x_4, x_32, x_14);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_apply_7(x_2, x_30, x_4, x_5, x_6, x_7, x_8, x_34);
return x_35;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("debug", 5);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" is type former", 15);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; lean_object* x_23; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
lean_inc(x_12);
x_22 = l_Lean_Compiler_LCNF_Param_toExpr(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_23 = l_Lean_Compiler_LCNF_inferType(x_22, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_26 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(x_24, x_4, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_box(0);
x_31 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___lambda__1(x_12, x_30, x_4, x_5, x_6, x_7, x_8, x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_15 = x_32;
x_16 = x_33;
goto block_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_dec(x_26);
lean_inc(x_12);
x_35 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___lambda__1___boxed), 8, 1);
lean_closure_set(x_35, 0, x_12);
x_36 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__3;
x_37 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1(x_36, x_4, x_5, x_6, x_7, x_8, x_34);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_42 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___lambda__2(x_12, x_35, x_41, x_4, x_5, x_6, x_7, x_8, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_15 = x_43;
x_16 = x_44;
goto block_21;
}
else
{
uint8_t x_45; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 0);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_42);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
lean_dec(x_37);
x_50 = lean_ctor_get(x_12, 1);
lean_inc(x_50);
x_51 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__8;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__5;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_addTrace___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__2(x_36, x_55, x_4, x_5, x_6, x_7, x_8, x_49);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_59 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___lambda__2(x_12, x_35, x_57, x_4, x_5, x_6, x_7, x_8, x_58);
lean_dec(x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_15 = x_60;
x_16 = x_61;
goto block_21;
}
else
{
uint8_t x_62; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_62 = !lean_is_exclusive(x_59);
if (x_62 == 0)
{
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
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
uint8_t x_66; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_66 = !lean_is_exclusive(x_26);
if (x_66 == 0)
{
return x_26;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_26, 0);
x_68 = lean_ctor_get(x_26, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_26);
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
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_23);
if (x_70 == 0)
{
return x_23;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_23, 0);
x_72 = lean_ctor_get(x_23, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_23);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
block_21:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_14, x_2, x_15);
x_2 = x_18;
x_3 = x_19;
x_9 = x_16;
goto _start;
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
x_14 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3(x_12, x_13, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
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
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndRec___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_8);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
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
x_18 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11;
x_19 = l_Lean_Expr_isAppOf(x_1, x_18);
x_20 = lean_array_get_size(x_14);
x_21 = lean_unsigned_to_nat(5u);
lean_inc(x_14);
x_22 = l_Array_toSubarray___rarg(x_14, x_21, x_20);
x_23 = l_Array_ofSubarray___rarg(x_22);
if (x_16 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_63 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_62);
x_24 = x_63;
goto block_61;
}
else
{
lean_object* x_64; 
x_64 = lean_array_fget(x_14, x_8);
x_24 = x_64;
goto block_61;
}
block_61:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(x_24);
x_26 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndRec___closed__1;
x_27 = lean_array_push(x_26, x_25);
if (x_17 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_59 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_58);
x_28 = x_59;
goto block_57;
}
else
{
lean_object* x_60; 
x_60 = lean_array_fget(x_14, x_12);
x_28 = x_60;
goto block_57;
}
block_57:
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(x_28);
x_30 = lean_array_push(x_27, x_29);
if (x_19 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(4u);
x_32 = lean_nat_dec_lt(x_31, x_15);
lean_dec(x_15);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_14);
x_33 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_34 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_33);
x_35 = l_Lean_Expr_beta(x_34, x_30);
x_36 = l_Lean_mkAppN(x_35, x_23);
x_37 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 7, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_21, x_37, x_2, x_3, x_4, x_5, x_6, x_7);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_array_fget(x_14, x_31);
lean_dec(x_14);
x_40 = l_Lean_Expr_beta(x_39, x_30);
x_41 = l_Lean_mkAppN(x_40, x_23);
x_42 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 7, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_21, x_42, x_2, x_3, x_4, x_5, x_6, x_7);
return x_43;
}
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_unsigned_to_nat(3u);
x_45 = lean_nat_dec_lt(x_44, x_15);
lean_dec(x_15);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_14);
x_46 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_47 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_46);
x_48 = l_Lean_Expr_beta(x_47, x_30);
x_49 = l_Lean_mkAppN(x_48, x_23);
x_50 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 7, 1);
lean_closure_set(x_50, 0, x_49);
x_51 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_21, x_50, x_2, x_3, x_4, x_5, x_6, x_7);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_array_fget(x_14, x_44);
lean_dec(x_14);
x_53 = l_Lean_Expr_beta(x_52, x_30);
x_54 = l_Lean_mkAppN(x_53, x_23);
x_55 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 7, 1);
lean_closure_set(x_55, 0, x_54);
x_56 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_21, x_55, x_2, x_3, x_4, x_5, x_6, x_7);
return x_56;
}
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
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_105; uint8_t x_106; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_105 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9;
x_106 = l_Lean_Expr_isAppOf(x_2, x_105);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__5;
x_108 = l_Lean_Expr_isAppOf(x_2, x_107);
lean_dec(x_2);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_array_get_size(x_1);
x_110 = lean_unsigned_to_nat(5u);
x_111 = lean_nat_dec_lt(x_110, x_109);
lean_dec(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_113 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_112);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_114 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_113, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_115);
x_117 = l_Lean_Compiler_LCNF_inferType(x_115, x_5, x_6, x_7, x_8, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_11);
x_120 = l_Lean_Compiler_LCNF_compatibleTypes(x_118, x_11, x_5, x_6, x_7, x_8, x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
x_124 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_125 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_115, x_124, x_4, x_5, x_6, x_7, x_8, x_123);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_128 = l_Lean_Compiler_LCNF_mkLcCast(x_126, x_11, x_5, x_6, x_7, x_8, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_unsigned_to_nat(6u);
x_132 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_129, x_1, x_131, x_4, x_5, x_6, x_7, x_8, x_130);
return x_132;
}
else
{
uint8_t x_133; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_128);
if (x_133 == 0)
{
return x_128;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_128, 0);
x_135 = lean_ctor_get(x_128, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_128);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_125);
if (x_137 == 0)
{
return x_125;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_125, 0);
x_139 = lean_ctor_get(x_125, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_125);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_11);
x_141 = lean_ctor_get(x_120, 1);
lean_inc(x_141);
lean_dec(x_120);
x_142 = lean_unsigned_to_nat(6u);
x_143 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_115, x_1, x_142, x_4, x_5, x_6, x_7, x_8, x_141);
return x_143;
}
}
else
{
uint8_t x_144; 
lean_dec(x_115);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
lean_dec(x_115);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_117);
if (x_148 == 0)
{
return x_117;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_117, 0);
x_150 = lean_ctor_get(x_117, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_117);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_114);
if (x_152 == 0)
{
return x_114;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_114, 0);
x_154 = lean_ctor_get(x_114, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_114);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_array_fget(x_1, x_110);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_157 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_156, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_158);
x_160 = l_Lean_Compiler_LCNF_inferType(x_158, x_5, x_6, x_7, x_8, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_11);
x_163 = l_Lean_Compiler_LCNF_compatibleTypes(x_161, x_11, x_5, x_6, x_7, x_8, x_162);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; uint8_t x_165; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_unbox(x_164);
lean_dec(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
x_167 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_168 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_158, x_167, x_4, x_5, x_6, x_7, x_8, x_166);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_171 = l_Lean_Compiler_LCNF_mkLcCast(x_169, x_11, x_5, x_6, x_7, x_8, x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_unsigned_to_nat(6u);
x_175 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_172, x_1, x_174, x_4, x_5, x_6, x_7, x_8, x_173);
return x_175;
}
else
{
uint8_t x_176; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_176 = !lean_is_exclusive(x_171);
if (x_176 == 0)
{
return x_171;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_171, 0);
x_178 = lean_ctor_get(x_171, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_171);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_180 = !lean_is_exclusive(x_168);
if (x_180 == 0)
{
return x_168;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_168, 0);
x_182 = lean_ctor_get(x_168, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_168);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_11);
x_184 = lean_ctor_get(x_163, 1);
lean_inc(x_184);
lean_dec(x_163);
x_185 = lean_unsigned_to_nat(6u);
x_186 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_158, x_1, x_185, x_4, x_5, x_6, x_7, x_8, x_184);
return x_186;
}
}
else
{
uint8_t x_187; 
lean_dec(x_158);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_187 = !lean_is_exclusive(x_163);
if (x_187 == 0)
{
return x_163;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_163, 0);
x_189 = lean_ctor_get(x_163, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_163);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_158);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_191 = !lean_is_exclusive(x_160);
if (x_191 == 0)
{
return x_160;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_160, 0);
x_193 = lean_ctor_get(x_160, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_160);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_195 = !lean_is_exclusive(x_157);
if (x_195 == 0)
{
return x_157;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_157, 0);
x_197 = lean_ctor_get(x_157, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_157);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
}
else
{
lean_object* x_199; 
x_199 = lean_box(0);
x_13 = x_199;
goto block_104;
}
}
else
{
lean_object* x_200; 
lean_dec(x_2);
x_200 = lean_box(0);
x_13 = x_200;
goto block_104;
}
block_104:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_13);
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_dec_lt(x_15, x_14);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_18 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_18, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_20);
x_22 = l_Lean_Compiler_LCNF_inferType(x_20, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_11);
x_25 = l_Lean_Compiler_LCNF_compatibleTypes(x_23, x_11, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_30 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_20, x_29, x_4, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l_Lean_Compiler_LCNF_mkLcCast(x_31, x_11, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_unsigned_to_nat(6u);
x_37 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_34, x_1, x_36, x_4, x_5, x_6, x_7, x_8, x_35);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
else
{
uint8_t x_42; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_30);
if (x_42 == 0)
{
return x_30;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_30, 0);
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_30);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_11);
x_46 = lean_ctor_get(x_25, 1);
lean_inc(x_46);
lean_dec(x_25);
x_47 = lean_unsigned_to_nat(6u);
x_48 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_20, x_1, x_47, x_4, x_5, x_6, x_7, x_8, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_25);
if (x_49 == 0)
{
return x_25;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_25, 0);
x_51 = lean_ctor_get(x_25, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_25);
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
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
uint8_t x_57; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_19);
if (x_57 == 0)
{
return x_19;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_19, 0);
x_59 = lean_ctor_get(x_19, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_19);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_array_fget(x_1, x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_62 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_61, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_63);
x_65 = l_Lean_Compiler_LCNF_inferType(x_63, x_5, x_6, x_7, x_8, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_11);
x_68 = l_Lean_Compiler_LCNF_compatibleTypes(x_66, x_11, x_5, x_6, x_7, x_8, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_73 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_63, x_72, x_4, x_5, x_6, x_7, x_8, x_71);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_76 = l_Lean_Compiler_LCNF_mkLcCast(x_74, x_11, x_5, x_6, x_7, x_8, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_unsigned_to_nat(6u);
x_80 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_77, x_1, x_79, x_4, x_5, x_6, x_7, x_8, x_78);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_76);
if (x_81 == 0)
{
return x_76;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_76, 0);
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_76);
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
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_73);
if (x_85 == 0)
{
return x_73;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_73, 0);
x_87 = lean_ctor_get(x_73, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_73);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_11);
x_89 = lean_ctor_get(x_68, 1);
lean_inc(x_89);
lean_dec(x_68);
x_90 = lean_unsigned_to_nat(6u);
x_91 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_63, x_1, x_90, x_4, x_5, x_6, x_7, x_8, x_89);
return x_91;
}
}
else
{
uint8_t x_92; 
lean_dec(x_63);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_68);
if (x_92 == 0)
{
return x_68;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_68, 0);
x_94 = lean_ctor_get(x_68, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_68);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_63);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_65);
if (x_96 == 0)
{
return x_65;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_65, 0);
x_98 = lean_ctor_get(x_65, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_65);
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
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_62);
if (x_100 == 0)
{
return x_62;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_62, 0);
x_102 = lean_ctor_get(x_62, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_62);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_201 = !lean_is_exclusive(x_10);
if (x_201 == 0)
{
return x_10;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_10, 0);
x_203 = lean_ctor_get(x_10, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_10);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_8);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
lean_inc(x_9);
x_11 = lean_mk_array(x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_9, x_12);
lean_dec(x_9);
lean_inc(x_1);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_11, x_13);
x_15 = l_Lean_Expr_getAppFn(x_1);
x_16 = lean_unsigned_to_nat(6u);
lean_inc(x_14);
x_17 = l_Array_toSubarray___rarg(x_14, x_8, x_16);
x_18 = l_Array_ofSubarray___rarg(x_17);
x_19 = l_Lean_mkAppN(x_15, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___boxed), 7, 1);
lean_closure_set(x_21, 0, x_20);
lean_inc(x_1);
x_22 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___lambda__2), 9, 2);
lean_closure_set(x_22, 0, x_14);
lean_closure_set(x_22, 1, x_1);
x_23 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 8, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_16, x_23, x_2, x_3, x_4, x_5, x_6, x_7);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lean_Expr_getAppFn(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_10);
x_12 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
lean_inc(x_11);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_11, x_14);
lean_dec(x_11);
lean_inc(x_2);
x_16 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_13, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault), 8, 2);
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
x_3 = lean_unsigned_to_nat(558u);
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
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_72; uint8_t x_73; 
x_72 = lean_unsigned_to_nat(5u);
x_73 = lean_nat_dec_lt(x_72, x_5);
lean_dec(x_5);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_75 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_74);
x_13 = x_75;
goto block_71;
}
else
{
lean_object* x_76; 
x_76 = lean_array_fget(x_4, x_72);
x_13 = x_76;
goto block_71;
}
block_71:
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_box(0);
lean_ctor_set(x_21, 1, x_28);
lean_ctor_set(x_21, 0, x_27);
x_29 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__4;
x_30 = l_Lean_Expr_const___override(x_29, x_21);
x_31 = l_Lean_mkApp3(x_30, x_2, x_3, x_15);
x_32 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_33 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_31, x_32, x_7, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Expr_app___override(x_6, x_34);
x_37 = lean_unsigned_to_nat(6u);
x_38 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_36, x_4, x_37, x_7, x_8, x_9, x_10, x_11, x_35);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
else
{
lean_object* x_43; lean_object* x_44; 
lean_free_object(x_21);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2;
x_44 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_43, x_7, x_8, x_9, x_10, x_11, x_16);
return x_44;
}
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_dec(x_21);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_18, 0);
lean_inc(x_46);
lean_dec(x_18);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__4;
x_50 = l_Lean_Expr_const___override(x_49, x_48);
x_51 = l_Lean_mkApp3(x_50, x_2, x_3, x_15);
x_52 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_53 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_51, x_52, x_7, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Expr_app___override(x_6, x_54);
x_57 = lean_unsigned_to_nat(6u);
x_58 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_56, x_4, x_57, x_7, x_8, x_9, x_10, x_11, x_55);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_61 = x_53;
} else {
 lean_dec_ref(x_53);
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
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_45);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2;
x_64 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_63, x_7, x_8, x_9, x_10, x_11, x_16);
return x_64;
}
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2;
x_66 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_65, x_7, x_8, x_9, x_10, x_11, x_16);
return x_66;
}
}
else
{
uint8_t x_67; 
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
x_67 = !lean_is_exclusive(x_14);
if (x_67 == 0)
{
return x_14;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_14, 0);
x_69 = lean_ctor_get(x_14, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_14);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
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
x_10 = l_Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
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
x_39 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_40 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_39);
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
x_35 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_36 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_35);
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
x_23 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_24 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_23);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__8(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault___spec__1(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__1 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__1();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__1);
l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__2 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__2();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__2);
l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__3 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__3();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__3);
l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__4 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__4();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__4);
l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__5 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__5();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__5);
l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__6 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__6();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_bindCases_go___spec__8___closed__6);
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
l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4 = _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4);
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
l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_applyToAny___lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_applyToAny___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_applyToAny___lambda__1___closed__1);
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
l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__3 = _init_l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__3();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__3);
l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__4 = _init_l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__4();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__4);
l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__4 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__4);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__5 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__5);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__6 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__6);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__7 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__7);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__8 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__8);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__9 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__9);
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
l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__1___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__4);
l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__5 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___spec__3___closed__5);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndRec___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndRec___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndRec___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__4 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__4);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
