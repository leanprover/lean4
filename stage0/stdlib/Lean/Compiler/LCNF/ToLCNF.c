// Lean compiler output
// Module: Lean.Compiler.LCNF.ToLCNF
// Imports: Init Lean.ProjFns Lean.Compiler.LCNF.Types Lean.Compiler.LCNF.Bind Lean.Compiler.LCNF.InferType Lean.Compiler.LCNF.Util
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__8___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__3;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_anyTypeExpr;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__21;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_mkLcCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__6;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__4;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__23;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__1;
extern lean_object* l_Lean_noConfusionExt;
lean_object* l_Lean_Compiler_LCNF_mkParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__11;
static size_t l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_let_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_cache___default___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2;
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__7(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__3;
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__4___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_isLCProof(lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__4;
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default___spec__1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Param_toExpr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__6;
lean_object* l_Lean_Meta_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3;
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__2;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__2;
static lean_object* l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2___closed__1;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__19;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__16;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__1(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Compiler_LCNF_ToLCNF_etaExpandN___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedProjectionFunctionInfo;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__1(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__27;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___closed__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instHashableExpr;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17;
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__2;
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8;
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__3;
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4;
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__1;
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__8(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___closed__1;
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__3(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__1;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__1;
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default___spec__1(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10___closed__2;
size_t lean_usize_modn(size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getCasesInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__3;
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1;
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6(lean_object*, uint8_t, lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_toCtorIfLit(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
extern lean_object* l_Lean_projectionFnInfoExt;
lean_object* l_Lean_Compiler_LCNF_Code_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_builtinRuntimeTypes;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__5;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__25;
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__4;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__7;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Compiler_LCNF_ToLCNF_etaExpandN___spec__1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__3;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__26;
uint8_t l_Lean_Compiler_LCNF_compatibleTypes(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__4;
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getCtorArity_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__5;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__20;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__8;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10___closed__1;
extern lean_object* l_Lean_Expr_instBEqExpr;
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__14;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__28;
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__2;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__18;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__3;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__1;
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__5;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__6;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_cache___default;
static lean_object* l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__3;
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__8(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__3;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndRec___closed__1;
lean_object* l_Lean_Expr_isConstructorApp_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7;
lean_object* l_Std_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__24;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_State_seq___default;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__7;
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__9;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Lean_Expr_fvar___override(x_2);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___lambda__1___closed__1;
x_10 = lean_array_push(x_9, x_8);
lean_inc(x_7);
x_11 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_jp", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__3;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4;
x_3 = lean_unsigned_to_nat(77u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__5;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_174; uint8_t x_175; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_2, x_11);
lean_dec(x_2);
x_174 = lean_array_get_size(x_1);
x_175 = lean_nat_dec_lt(x_12, x_174);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_177 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___spec__1(x_176);
switch (lean_obj_tag(x_177)) {
case 0:
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec(x_177);
x_179 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_3);
x_2 = x_12;
x_3 = x_179;
goto _start;
}
case 1:
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_177, 0);
lean_inc(x_181);
lean_dec(x_177);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_3);
x_2 = x_12;
x_3 = x_182;
goto _start;
}
case 2:
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_177, 0);
lean_inc(x_184);
lean_dec(x_177);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_3);
x_2 = x_12;
x_3 = x_185;
goto _start;
}
case 3:
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_177, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_177, 1);
lean_inc(x_188);
lean_dec(x_177);
x_13 = x_187;
x_14 = x_188;
goto block_173;
}
default: 
{
lean_object* x_189; 
lean_dec(x_12);
x_189 = l_Lean_Compiler_LCNF_Code_inferType(x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_189) == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_189, 0);
x_192 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_189, 0, x_192);
return x_189;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_189, 0);
x_194 = lean_ctor_get(x_189, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_189);
x_195 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_195, 0, x_193);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
else
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_189);
if (x_197 == 0)
{
return x_189;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_189, 0);
x_199 = lean_ctor_get(x_189, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_189);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
}
}
else
{
lean_object* x_201; 
x_201 = lean_array_fget(x_1, x_12);
switch (lean_obj_tag(x_201)) {
case 0:
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
lean_dec(x_201);
x_203 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_3);
x_2 = x_12;
x_3 = x_203;
goto _start;
}
case 1:
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_201, 0);
lean_inc(x_205);
lean_dec(x_201);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_3);
x_2 = x_12;
x_3 = x_206;
goto _start;
}
case 2:
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_201, 0);
lean_inc(x_208);
lean_dec(x_201);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_3);
x_2 = x_12;
x_3 = x_209;
goto _start;
}
case 3:
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_201, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_201, 1);
lean_inc(x_212);
lean_dec(x_201);
x_13 = x_211;
x_14 = x_212;
goto block_173;
}
default: 
{
lean_object* x_213; 
lean_dec(x_12);
x_213 = l_Lean_Compiler_LCNF_Code_inferType(x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_213) == 0)
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_213, 0);
x_216 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_213, 0, x_216);
return x_213;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_217 = lean_ctor_get(x_213, 0);
x_218 = lean_ctor_get(x_213, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_213);
x_219 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_219, 0, x_217);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_218);
return x_220;
}
}
else
{
uint8_t x_221; 
x_221 = !lean_is_exclusive(x_213);
if (x_221 == 0)
{
return x_213;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_213, 0);
x_223 = lean_ctor_get(x_213, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_213);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
}
}
block_173:
{
switch (lean_obj_tag(x_3)) {
case 2:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(x_13, x_3, x_15, x_4, x_5, x_6, x_7);
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_3, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_3, 0);
lean_dec(x_19);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_14);
lean_inc(x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___lambda__1___boxed), 6, 1);
lean_closure_set(x_23, 0, x_20);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_Compiler_LCNF_Code_bind(x_22, x_23, x_4, x_5, x_6, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_ctor_set(x_3, 1, x_25);
lean_ctor_set(x_3, 0, x_20);
x_2 = x_12;
x_7 = x_26;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_20);
lean_free_object(x_3);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
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
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_16, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_38, 0, x_14);
lean_inc(x_36);
x_39 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___lambda__1___boxed), 6, 1);
lean_closure_set(x_39, 0, x_36);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_40 = l_Lean_Compiler_LCNF_Code_bind(x_38, x_39, x_4, x_5, x_6, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_41);
x_2 = x_12;
x_3 = x_43;
x_7 = x_42;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_36);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_47 = x_40;
} else {
 lean_dec_ref(x_40);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_49 = lean_ctor_get(x_16, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_16, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_51 = x_16;
} else {
 lean_dec_ref(x_16);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
case 4:
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_54 = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(x_13, x_3, x_53, x_4, x_5, x_6, x_7);
x_55 = !lean_is_exclusive(x_3);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_3, 0);
lean_dec(x_56);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
lean_ctor_set(x_3, 0, x_14);
lean_inc(x_57);
x_59 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___lambda__1___boxed), 6, 1);
lean_closure_set(x_59, 0, x_57);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_60 = l_Lean_Compiler_LCNF_Code_bind(x_3, x_59, x_4, x_5, x_6, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_61);
x_2 = x_12;
x_3 = x_63;
x_7 = x_62;
goto _start;
}
else
{
uint8_t x_65; 
lean_dec(x_57);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
return x_60;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_60, 0);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_60);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_54);
if (x_69 == 0)
{
return x_54;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_54, 0);
x_71 = lean_ctor_get(x_54, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_54);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_54, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_54, 1);
lean_inc(x_74);
lean_dec(x_54);
x_75 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_75, 0, x_14);
lean_inc(x_73);
x_76 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___lambda__1___boxed), 6, 1);
lean_closure_set(x_76, 0, x_73);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_77 = l_Lean_Compiler_LCNF_Code_bind(x_75, x_76, x_4, x_5, x_6, x_74);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_73);
lean_ctor_set(x_80, 1, x_78);
x_2 = x_12;
x_3 = x_80;
x_7 = x_79;
goto _start;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_73);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_84 = x_77;
} else {
 lean_dec_ref(x_77);
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
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_86 = lean_ctor_get(x_54, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_54, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_88 = x_54;
} else {
 lean_dec_ref(x_54);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
case 5:
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_3, 0);
lean_inc(x_90);
x_91 = lean_name_eq(x_13, x_90);
lean_dec(x_90);
lean_dec(x_13);
if (x_91 == 0)
{
lean_dec(x_14);
x_2 = x_12;
goto _start;
}
else
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_3);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_3, 0);
lean_dec(x_94);
lean_ctor_set_tag(x_3, 4);
lean_ctor_set(x_3, 0, x_14);
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_96; 
lean_dec(x_3);
x_96 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_96, 0, x_14);
x_2 = x_12;
x_3 = x_96;
goto _start;
}
}
}
case 6:
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_99 = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(x_13, x_3, x_98, x_4, x_5, x_6, x_7);
x_100 = !lean_is_exclusive(x_3);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_3, 0);
lean_dec(x_101);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
lean_dec(x_99);
lean_ctor_set_tag(x_3, 4);
lean_ctor_set(x_3, 0, x_14);
lean_inc(x_102);
x_104 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___lambda__1___boxed), 6, 1);
lean_closure_set(x_104, 0, x_102);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_105 = l_Lean_Compiler_LCNF_Code_bind(x_3, x_104, x_4, x_5, x_6, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_102);
lean_ctor_set(x_108, 1, x_106);
x_2 = x_12;
x_3 = x_108;
x_7 = x_107;
goto _start;
}
else
{
uint8_t x_110; 
lean_dec(x_102);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_110 = !lean_is_exclusive(x_105);
if (x_110 == 0)
{
return x_105;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_105, 0);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_105);
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
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_114 = !lean_is_exclusive(x_99);
if (x_114 == 0)
{
return x_99;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_99, 0);
x_116 = lean_ctor_get(x_99, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_99);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_ctor_get(x_99, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_99, 1);
lean_inc(x_119);
lean_dec(x_99);
x_120 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_120, 0, x_14);
lean_inc(x_118);
x_121 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___lambda__1___boxed), 6, 1);
lean_closure_set(x_121, 0, x_118);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_122 = l_Lean_Compiler_LCNF_Code_bind(x_120, x_121, x_4, x_5, x_6, x_119);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_125, 0, x_118);
lean_ctor_set(x_125, 1, x_123);
x_2 = x_12;
x_3 = x_125;
x_7 = x_124;
goto _start;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_118);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_127 = lean_ctor_get(x_122, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_122, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_129 = x_122;
} else {
 lean_dec_ref(x_122);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_131 = lean_ctor_get(x_99, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_99, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_133 = x_99;
} else {
 lean_dec_ref(x_99);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
}
default: 
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_136 = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(x_13, x_3, x_135, x_4, x_5, x_6, x_7);
x_137 = !lean_is_exclusive(x_3);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_3, 1);
lean_dec(x_138);
x_139 = lean_ctor_get(x_3, 0);
lean_dec(x_139);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_136, 1);
lean_inc(x_141);
lean_dec(x_136);
x_142 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_142, 0, x_14);
lean_inc(x_140);
x_143 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___lambda__1___boxed), 6, 1);
lean_closure_set(x_143, 0, x_140);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_144 = l_Lean_Compiler_LCNF_Code_bind(x_142, x_143, x_4, x_5, x_6, x_141);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
lean_ctor_set_tag(x_3, 2);
lean_ctor_set(x_3, 1, x_145);
lean_ctor_set(x_3, 0, x_140);
x_2 = x_12;
x_7 = x_146;
goto _start;
}
else
{
uint8_t x_148; 
lean_dec(x_140);
lean_free_object(x_3);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_148 = !lean_is_exclusive(x_144);
if (x_148 == 0)
{
return x_144;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_144, 0);
x_150 = lean_ctor_get(x_144, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_144);
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
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_152 = !lean_is_exclusive(x_136);
if (x_152 == 0)
{
return x_136;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_136, 0);
x_154 = lean_ctor_get(x_136, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_136);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_156 = lean_ctor_get(x_136, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_136, 1);
lean_inc(x_157);
lean_dec(x_136);
x_158 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_158, 0, x_14);
lean_inc(x_156);
x_159 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___lambda__1___boxed), 6, 1);
lean_closure_set(x_159, 0, x_156);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_160 = l_Lean_Compiler_LCNF_Code_bind(x_158, x_159, x_4, x_5, x_6, x_157);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_163, 0, x_156);
lean_ctor_set(x_163, 1, x_161);
x_2 = x_12;
x_3 = x_163;
x_7 = x_162;
goto _start;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_156);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_165 = lean_ctor_get(x_160, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_160, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_167 = x_160;
} else {
 lean_dec_ref(x_160);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_169 = lean_ctor_get(x_136, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_136, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_171 = x_136;
} else {
 lean_dec_ref(x_136);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_x", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_array_get_size(x_1);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go(x_1, x_8, x_9, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__2;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_2, x_11, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_array_push(x_1, x_15);
x_17 = lean_array_get_size(x_16);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go(x_16, x_17, x_19, x_3, x_4, x_5, x_14);
lean_dec(x_16);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__5;
x_3 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__4;
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
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__3;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__6;
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
x_1 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_cache___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__2;
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
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_typeCache___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at_Lean_Compiler_LCNF_ToLCNF_State_isTypeFormerTypeCache___default___spec__1(x_1);
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
x_1 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__2;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__2;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__2;
x_3 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__3;
x_4 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__4;
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
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__9() {
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
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__10() {
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
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__2;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__6;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__8;
x_3 = l_Lean_Compiler_LCNF_ToLCNF_State_cache___default___closed__1;
x_4 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__11;
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
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__5;
x_3 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__12;
x_4 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__6;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_2, x_8);
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
x_18 = lean_st_ref_get(x_5, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__13;
x_21 = lean_st_mk_ref(x_20, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_5);
lean_inc(x_22);
x_24 = lean_apply_5(x_1, x_17, x_22, x_4, x_5, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_get(x_5, x_26);
lean_dec(x_5);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_get(x_22, x_28);
lean_dec(x_22);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_25);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_22);
lean_dec(x_5);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 4);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode(x_12, x_1, x_3, x_4, x_5, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_toCode(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_take(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 4);
x_14 = lean_array_push(x_13, x_1);
lean_ctor_set(x_10, 4, x_14);
x_15 = lean_st_ref_set(x_2, x_10, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
x_25 = lean_ctor_get(x_10, 3);
x_26 = lean_ctor_get(x_10, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_27 = lean_array_push(x_26, x_1);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_25);
lean_ctor_set(x_28, 4, x_27);
x_29 = lean_st_ref_set(x_2, x_28, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_pushElement(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_box(4);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_pushElement(x_7, x_2, x_3, x_4, x_5, x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Compiler_LCNF_mkAuxParam(x_1, x_3, x_4, x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Expr_fvar___override(x_13);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_fvar___override(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isFVar(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Compiler_LCNF_mkFreshBinderName(x_2, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_12 = l_Lean_Compiler_LCNF_inferType(x_1, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Compiler_LCNF_mkLetDecl(x_10, x_13, x_1, x_4, x_5, x_6, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_16);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = l_Lean_Compiler_LCNF_ToLCNF_pushElement(x_18, x_3, x_4, x_5, x_6, x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = l_Lean_Expr_fvar___override(x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
x_26 = l_Lean_Expr_fvar___override(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_7);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__7;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_State_cache___default___closed__1;
x_3 = l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__1;
x_4 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__2;
x_9 = lean_st_mk_ref(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_10);
x_12 = lean_apply_5(x_1, x_10, x_2, x_3, x_4, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_4, x_14);
lean_dec(x_4);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_10, x_16);
lean_dec(x_10);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_run___rarg), 5, 0);
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
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__5(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__5(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
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
x_10 = l_Std_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6(x_1, x_2, x_8);
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
x_16 = l_Std_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6(x_1, x_2, x_14);
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
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
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
x_12 = l_Std_AssocList_contains___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__2(x_2, x_11);
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
x_18 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_14);
x_19 = lean_nat_dec_le(x_18, x_7);
lean_dec(x_7);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_1);
x_20 = l_Std_HashMapImp_expand___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__3(x_14, x_17);
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
x_21 = l_Std_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6(x_2, x_3, x_11);
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
x_30 = l_Std_AssocList_contains___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__2(x_2, x_29);
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
x_36 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_32);
x_37 = lean_nat_dec_le(x_36, x_25);
lean_dec(x_25);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = l_Std_HashMapImp_expand___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__3(x_32, x_35);
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
x_40 = l_Std_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6(x_2, x_3, x_29);
x_41 = lean_array_uset(x_24, x_28, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_23);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__8(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__7(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__8(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_3, x_9);
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
x_21 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__13;
x_22 = lean_st_mk_ref(x_21, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_6);
lean_inc(x_23);
lean_inc(x_1);
x_25 = l_Lean_Meta_isTypeFormerType(x_1, x_18, x_23, x_5, x_6, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_6, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_get(x_23, x_29);
lean_dec(x_23);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_st_ref_get(x_6, x_31);
lean_dec(x_6);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_st_ref_take(x_3, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_35, 3);
x_39 = lean_unbox(x_26);
x_40 = l_Std_HashMap_insert___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__1(x_38, x_1, x_39);
lean_ctor_set(x_35, 3, x_40);
x_41 = lean_st_ref_set(x_3, x_35, x_36);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_26);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_26);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_46 = lean_ctor_get(x_35, 0);
x_47 = lean_ctor_get(x_35, 1);
x_48 = lean_ctor_get(x_35, 2);
x_49 = lean_ctor_get(x_35, 3);
x_50 = lean_ctor_get(x_35, 4);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_35);
x_51 = lean_unbox(x_26);
x_52 = l_Std_HashMap_insert___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__1(x_49, x_1, x_51);
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_47);
lean_ctor_set(x_53, 2, x_48);
lean_ctor_set(x_53, 3, x_52);
lean_ctor_set(x_53, 4, x_50);
x_54 = lean_st_ref_set(x_3, x_53, x_36);
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
lean_ctor_set(x_57, 0, x_26);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_25);
if (x_58 == 0)
{
return x_25;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_25, 0);
x_60 = lean_ctor_get(x_25, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_25);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(x_11, x_1);
switch (x_12) {
case 0:
{
uint8_t x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = 0;
x_14 = lean_box(x_13);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
case 1:
{
uint8_t x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = 1;
x_16 = lean_box(x_15);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
default: 
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_free_object(x_7);
x_17 = lean_st_ref_get(x_5, x_10);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_2, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_21, 3);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_1);
x_24 = l_Std_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__7(x_23, x_1);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_19);
x_25 = lean_box(0);
x_26 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1(x_1, x_25, x_2, x_3, x_4, x_5, x_22);
lean_dec(x_3);
lean_dec(x_2);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
lean_ctor_set(x_19, 0, x_27);
return x_19;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_ctor_get(x_28, 3);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_1);
x_31 = l_Std_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__7(x_30, x_1);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(0);
x_33 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1(x_1, x_32, x_2, x_3, x_4, x_5, x_29);
lean_dec(x_3);
lean_dec(x_2);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
return x_35;
}
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_7, 0);
x_37 = lean_ctor_get(x_7, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_7);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(x_38, x_1);
switch (x_39) {
case 0:
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = 0;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
case 1:
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = 1;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_37);
return x_45;
}
default: 
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_st_ref_get(x_5, x_37);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_st_ref_get(x_2, x_47);
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
x_52 = lean_ctor_get(x_49, 3);
lean_inc(x_52);
lean_dec(x_49);
lean_inc(x_1);
x_53 = l_Std_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__7(x_52, x_1);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_51);
x_54 = lean_box(0);
x_55 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1(x_1, x_54, x_2, x_3, x_4, x_5, x_50);
lean_dec(x_3);
lean_dec(x_2);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
lean_dec(x_53);
if (lean_is_scalar(x_51)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_51;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_50);
return x_57;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Std_AssocList_replace___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__6(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Std_HashMap_insert___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__1(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___spec__8(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 4);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_st_ref_get(x_5, x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_take(x_2, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_18, 4);
lean_dec(x_21);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
lean_ctor_set(x_18, 4, x_22);
x_23 = lean_st_ref_set(x_2, x_18, x_19);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_5);
lean_inc(x_2);
x_25 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_5, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_get(x_2, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_5, x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_st_ref_get(x_2, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_31, 2);
lean_inc(x_38);
lean_dec(x_31);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_40 = lean_ctor_get(x_36, 4);
lean_dec(x_40);
x_41 = lean_ctor_get(x_36, 2);
lean_dec(x_41);
x_42 = lean_ctor_get(x_36, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_36, 0);
lean_dec(x_43);
lean_ctor_set(x_36, 4, x_14);
lean_ctor_set(x_36, 2, x_38);
lean_ctor_set(x_36, 1, x_13);
lean_ctor_set(x_36, 0, x_12);
x_44 = lean_st_ref_get(x_5, x_37);
lean_dec(x_5);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_st_ref_set(x_2, x_36, x_45);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_26);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_26);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_36, 3);
lean_inc(x_51);
lean_dec(x_36);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_13);
lean_ctor_set(x_52, 2, x_38);
lean_ctor_set(x_52, 3, x_51);
lean_ctor_set(x_52, 4, x_14);
x_53 = lean_st_ref_get(x_5, x_37);
lean_dec(x_5);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_st_ref_set(x_2, x_52, x_54);
lean_dec(x_2);
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
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_26);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_59 = lean_ctor_get(x_25, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_25, 1);
lean_inc(x_60);
lean_dec(x_25);
x_61 = lean_st_ref_get(x_5, x_60);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_st_ref_get(x_2, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_st_ref_get(x_5, x_65);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_st_ref_get(x_2, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_64, 2);
lean_inc(x_71);
lean_dec(x_64);
x_72 = !lean_is_exclusive(x_69);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_73 = lean_ctor_get(x_69, 4);
lean_dec(x_73);
x_74 = lean_ctor_get(x_69, 2);
lean_dec(x_74);
x_75 = lean_ctor_get(x_69, 1);
lean_dec(x_75);
x_76 = lean_ctor_get(x_69, 0);
lean_dec(x_76);
lean_ctor_set(x_69, 4, x_14);
lean_ctor_set(x_69, 2, x_71);
lean_ctor_set(x_69, 1, x_13);
lean_ctor_set(x_69, 0, x_12);
x_77 = lean_st_ref_get(x_5, x_70);
lean_dec(x_5);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_st_ref_set(x_2, x_69, x_78);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
lean_ctor_set_tag(x_79, 1);
lean_ctor_set(x_79, 0, x_59);
return x_79;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_59);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_84 = lean_ctor_get(x_69, 3);
lean_inc(x_84);
lean_dec(x_69);
x_85 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_85, 0, x_12);
lean_ctor_set(x_85, 1, x_13);
lean_ctor_set(x_85, 2, x_71);
lean_ctor_set(x_85, 3, x_84);
lean_ctor_set(x_85, 4, x_14);
x_86 = lean_st_ref_get(x_5, x_70);
lean_dec(x_5);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_st_ref_set(x_2, x_85, x_87);
lean_dec(x_2);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
 lean_ctor_set_tag(x_91, 1);
}
lean_ctor_set(x_91, 0, x_59);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_92 = lean_ctor_get(x_18, 0);
x_93 = lean_ctor_get(x_18, 1);
x_94 = lean_ctor_get(x_18, 2);
x_95 = lean_ctor_get(x_18, 3);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_18);
x_96 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_97 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_93);
lean_ctor_set(x_97, 2, x_94);
lean_ctor_set(x_97, 3, x_95);
lean_ctor_set(x_97, 4, x_96);
x_98 = lean_st_ref_set(x_2, x_97, x_19);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
lean_inc(x_5);
lean_inc(x_2);
x_100 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_st_ref_get(x_5, x_102);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_st_ref_get(x_2, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_st_ref_get(x_5, x_107);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_st_ref_get(x_2, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_ctor_get(x_106, 2);
lean_inc(x_113);
lean_dec(x_106);
x_114 = lean_ctor_get(x_111, 3);
lean_inc(x_114);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 lean_ctor_release(x_111, 4);
 x_115 = x_111;
} else {
 lean_dec_ref(x_111);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 5, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_12);
lean_ctor_set(x_116, 1, x_13);
lean_ctor_set(x_116, 2, x_113);
lean_ctor_set(x_116, 3, x_114);
lean_ctor_set(x_116, 4, x_14);
x_117 = lean_st_ref_get(x_5, x_112);
lean_dec(x_5);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_119 = lean_st_ref_set(x_2, x_116, x_118);
lean_dec(x_2);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_101);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_123 = lean_ctor_get(x_100, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_100, 1);
lean_inc(x_124);
lean_dec(x_100);
x_125 = lean_st_ref_get(x_5, x_124);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_st_ref_get(x_2, x_126);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_st_ref_get(x_5, x_129);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_st_ref_get(x_2, x_131);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_128, 2);
lean_inc(x_135);
lean_dec(x_128);
x_136 = lean_ctor_get(x_133, 3);
lean_inc(x_136);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 lean_ctor_release(x_133, 2);
 lean_ctor_release(x_133, 3);
 lean_ctor_release(x_133, 4);
 x_137 = x_133;
} else {
 lean_dec_ref(x_133);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 5, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_12);
lean_ctor_set(x_138, 1, x_13);
lean_ctor_set(x_138, 2, x_135);
lean_ctor_set(x_138, 3, x_136);
lean_ctor_set(x_138, 4, x_14);
x_139 = lean_st_ref_get(x_5, x_134);
lean_dec(x_5);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_st_ref_set(x_2, x_138, x_140);
lean_dec(x_2);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
 lean_ctor_set_tag(x_144, 1);
}
lean_ctor_set(x_144, 0, x_123);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_withNewScope___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_AssocList_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__2(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__4(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__7(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__7(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_AssocList_replace___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__8(x_1, x_2, x_8);
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
x_15 = l_Std_AssocList_replace___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__8(x_1, x_2, x_13);
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
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_12 = l_Std_AssocList_contains___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__4(x_2, x_11);
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
x_19 = l_Std_HashMapImp_expand___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__5(x_14, x_16);
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
x_20 = l_Std_AssocList_replace___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__8(x_2, x_3, x_11);
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
x_29 = l_Std_AssocList_contains___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__4(x_2, x_28);
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
x_36 = l_Std_HashMapImp_expand___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__5(x_31, x_33);
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
x_38 = l_Std_AssocList_replace___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__8(x_2, x_3, x_28);
x_39 = lean_array_uset(x_23, x_27, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_2, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_1);
x_14 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__1(x_13, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_9);
x_15 = lean_st_ref_get(x_5, x_12);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_2, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
x_23 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set(x_25, 5, x_21);
x_26 = lean_st_ref_get(x_5, x_19);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__13;
x_29 = lean_st_mk_ref(x_28, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_5);
lean_inc(x_30);
lean_inc(x_1);
x_32 = l_Lean_Compiler_LCNF_toLCNFType(x_1, x_25, x_30, x_4, x_5, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_5, x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_get(x_30, x_36);
lean_dec(x_30);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_st_ref_get(x_5, x_38);
lean_dec(x_5);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_st_ref_take(x_2, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_42, 2);
lean_inc(x_33);
x_46 = l_Std_HashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__3(x_45, x_1, x_33);
lean_ctor_set(x_42, 2, x_46);
x_47 = lean_st_ref_set(x_2, x_42, x_43);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_33);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_33);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_52 = lean_ctor_get(x_42, 0);
x_53 = lean_ctor_get(x_42, 1);
x_54 = lean_ctor_get(x_42, 2);
x_55 = lean_ctor_get(x_42, 3);
x_56 = lean_ctor_get(x_42, 4);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_42);
lean_inc(x_33);
x_57 = l_Std_HashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__3(x_54, x_1, x_33);
x_58 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_53);
lean_ctor_set(x_58, 2, x_57);
lean_ctor_set(x_58, 3, x_55);
lean_ctor_set(x_58, 4, x_56);
x_59 = lean_st_ref_set(x_2, x_58, x_43);
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
lean_ctor_set(x_62, 0, x_33);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_30);
lean_dec(x_5);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_32);
if (x_63 == 0)
{
return x_32;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_32, 0);
x_65 = lean_ctor_get(x_32, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_32);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_67 = lean_ctor_get(x_14, 0);
lean_inc(x_67);
lean_dec(x_14);
lean_ctor_set(x_9, 0, x_67);
return x_9;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_9, 0);
x_69 = lean_ctor_get(x_9, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_9);
x_70 = lean_ctor_get(x_68, 2);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_1);
x_71 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__1(x_70, x_1);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_72 = lean_st_ref_get(x_5, x_69);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_st_ref_get(x_2, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_box(0);
x_79 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
x_80 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_77);
lean_ctor_set(x_82, 2, x_80);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_81);
lean_ctor_set(x_82, 5, x_78);
x_83 = lean_st_ref_get(x_5, x_76);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__13;
x_86 = lean_st_mk_ref(x_85, x_84);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_5);
lean_inc(x_87);
lean_inc(x_1);
x_89 = l_Lean_Compiler_LCNF_toLCNFType(x_1, x_82, x_87, x_4, x_5, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_st_ref_get(x_5, x_91);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_st_ref_get(x_87, x_93);
lean_dec(x_87);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_st_ref_get(x_5, x_95);
lean_dec(x_5);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_st_ref_take(x_2, x_97);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_99, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_99, 4);
lean_inc(x_105);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 lean_ctor_release(x_99, 2);
 lean_ctor_release(x_99, 3);
 lean_ctor_release(x_99, 4);
 x_106 = x_99;
} else {
 lean_dec_ref(x_99);
 x_106 = lean_box(0);
}
lean_inc(x_90);
x_107 = l_Std_HashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__3(x_103, x_1, x_90);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 5, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_101);
lean_ctor_set(x_108, 1, x_102);
lean_ctor_set(x_108, 2, x_107);
lean_ctor_set(x_108, 3, x_104);
lean_ctor_set(x_108, 4, x_105);
x_109 = lean_st_ref_set(x_2, x_108, x_100);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_90);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_1);
x_113 = lean_ctor_get(x_89, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_89, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_115 = x_89;
} else {
 lean_dec_ref(x_89);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_117 = lean_ctor_get(x_71, 0);
lean_inc(x_117);
lean_dec(x_71);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_69);
return x_118;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_Compiler_LCNF_ToLCNF_toLCNFType___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lean_Name_hasMacroScopes(x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_erase_macro_scopes(x_1);
x_9 = l_Lean_Compiler_LCNF_mkFreshBinderName(x_8, x_2, x_3, x_4, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(x_1, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
x_14 = l_Lean_Compiler_LCNF_mkParam(x_9, x_12, x_4, x_5, x_6, x_13);
lean_dec(x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_6, x_16);
lean_dec(x_6);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_take(x_3, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
x_25 = 0;
x_26 = lean_local_ctx_mk_local_decl(x_23, x_24, x_9, x_2, x_25);
lean_ctor_set(x_20, 0, x_26);
x_27 = lean_st_ref_set(x_3, x_20, x_21);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_15);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
x_34 = lean_ctor_get(x_20, 2);
x_35 = lean_ctor_get(x_20, 3);
x_36 = lean_ctor_get(x_20, 4);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_37 = lean_ctor_get(x_15, 0);
lean_inc(x_37);
x_38 = 0;
x_39 = lean_local_ctx_mk_local_decl(x_32, x_37, x_9, x_2, x_38);
x_40 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
lean_ctor_set(x_40, 2, x_34);
lean_ctor_set(x_40, 3, x_35);
lean_ctor_set(x_40, 4, x_36);
x_41 = lean_st_ref_set(x_3, x_40, x_21);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_15);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_11);
if (x_45 == 0)
{
return x_11;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_11, 0);
x_47 = lean_ctor_get(x_11, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_11);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_mkParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_11 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(x_1, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
x_14 = l_Lean_Compiler_LCNF_mkLetDecl(x_12, x_4, x_5, x_7, x_8, x_9, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_9, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_take(x_6, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 4);
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
x_26 = 0;
x_27 = lean_local_ctx_mk_let_decl(x_23, x_25, x_12, x_2, x_3, x_26);
lean_inc(x_15);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_15);
x_29 = lean_array_push(x_24, x_28);
lean_ctor_set(x_20, 4, x_29);
lean_ctor_set(x_20, 0, x_27);
x_30 = lean_st_ref_set(x_6, x_20, x_21);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_15);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
x_37 = lean_ctor_get(x_20, 2);
x_38 = lean_ctor_get(x_20, 3);
x_39 = lean_ctor_get(x_20, 4);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
x_41 = 0;
x_42 = lean_local_ctx_mk_let_decl(x_35, x_40, x_12, x_2, x_3, x_41);
lean_inc(x_15);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_15);
x_44 = lean_array_push(x_39, x_43);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_36);
lean_ctor_set(x_45, 2, x_37);
lean_ctor_set(x_45, 3, x_38);
lean_ctor_set(x_45, 4, x_44);
x_46 = lean_st_ref_set(x_6, x_45, x_21);
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
lean_ctor_set(x_49, 0, x_15);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_expr_instantiate_rev(x_10, x_2);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_mkParam(x_9, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
x_16 = l_Lean_Compiler_LCNF_Param_toExpr(x_14);
x_17 = lean_array_push(x_2, x_16);
x_18 = lean_array_push(x_3, x_14);
x_1 = x_11;
x_2 = x_17;
x_3 = x_18;
x_8 = x_15;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_7);
lean_dec(x_6);
x_24 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_8);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_8 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda_go(x_1, x_7, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_2, x_10);
if (x_11 == 0)
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_expr_instantiate_rev(x_13, x_3);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_mkParam(x_12, x_15, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_2, x_19);
lean_dec(x_2);
lean_inc(x_17);
x_21 = l_Lean_Compiler_LCNF_Param_toExpr(x_17);
x_22 = lean_array_push(x_3, x_21);
x_23 = lean_array_push(x_4, x_17);
x_1 = x_14;
x_2 = x_20;
x_3 = x_22;
x_4 = x_23;
x_9 = x_18;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_29 = lean_expr_instantiate_rev(x_1, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_9);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_32 = lean_expr_instantiate_rev(x_1, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_9 = l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go(x_1, x_2, x_8, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_st_ref_get(x_6, x_7);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
x_18 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_8);
lean_ctor_set(x_19, 5, x_16);
x_20 = lean_st_ref_get(x_6, x_14);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__13;
x_23 = lean_st_mk_ref(x_22, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_24);
lean_inc(x_19);
lean_inc(x_1);
x_26 = lean_infer_type(x_1, x_19, x_24, x_5, x_6, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_2);
x_30 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___lambda__1___boxed), 8, 1);
lean_closure_set(x_30, 0, x_1);
lean_inc(x_6);
lean_inc(x_24);
x_31 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Compiler_LCNF_ToLCNF_etaExpandN___spec__1___rarg(x_27, x_29, x_30, x_19, x_24, x_5, x_6, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_6, x_33);
lean_dec(x_6);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_get(x_24, x_35);
lean_dec(x_24);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_32);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_32);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_24);
lean_dec(x_6);
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
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_26);
if (x_45 == 0)
{
return x_26;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_26, 0);
x_47 = lean_ctor_get(x_26, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_26);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_7);
return x_49;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_17);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(x_1, x_17, x_3, x_4, x_5, x_6, x_7);
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
x_7 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__3(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_20 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static size_t _init_l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__2;
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
x_22 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
x_29 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
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
x_38 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2(x_35, x_36, x_37, x_4, x_5);
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
x_43 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__2;
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
x_64 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
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
x_75 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2(x_71, x_73, x_74, x_4, x_5);
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
x_84 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__4(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
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
x_92 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__3;
x_93 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__3(x_3, x_90, x_91, lean_box(0), x_83, x_92);
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
x_98 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__4(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
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
x_106 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__3;
x_107 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__3(x_3, x_104, x_105, lean_box(0), x_97, x_106);
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2(x_5, x_8, x_9, x_2, x_3);
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
x_18 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2(x_13, x_16, x_17, x_2, x_3);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__2;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__3;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = lean_st_ref_get(x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_15);
x_17 = lean_ctor_get(x_4, 2);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__5;
lean_inc(x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_1);
lean_inc(x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_24);
x_26 = lean_ctor_get(x_4, 2);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__5;
lean_inc(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_1);
lean_inc(x_7);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__8(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__2;
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
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Expr_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__8(x_3, x_5, x_2);
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
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10___closed__2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_2);
x_15 = l_Std_PersistentHashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__1(x_14, x_1, x_2);
lean_ctor_set(x_11, 1, x_15);
x_16 = lean_st_ref_set(x_3, x_11, x_12);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
x_23 = lean_ctor_get(x_11, 2);
x_24 = lean_ctor_get(x_11, 3);
x_25 = lean_ctor_get(x_11, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
lean_inc(x_2);
x_26 = l_Std_PersistentHashMap_insert___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__1(x_22, x_1, x_2);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_24);
lean_ctor_set(x_27, 4, x_25);
x_28 = lean_st_ref_set(x_3, x_27, x_12);
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
x_3 = lean_unsigned_to_nat(244u);
x_4 = lean_unsigned_to_nat(23u);
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
x_3 = lean_unsigned_to_nat(242u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_dec(x_2);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__4;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_10, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
case 2:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = l_Lean_indentExpr(x_1);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__6;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__8;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6(x_21, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
case 4:
{
lean_object* x_27; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_28, x_3, x_4, x_5, x_6, x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_30;
}
else
{
uint8_t x_31; 
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
case 5:
{
lean_object* x_35; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_35 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_36, x_3, x_4, x_5, x_6, x_37);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_38;
}
else
{
uint8_t x_39; 
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
case 6:
{
lean_object* x_43; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_43 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_44, x_3, x_4, x_5, x_6, x_45);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
case 7:
{
lean_object* x_51; lean_object* x_52; 
x_51 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__9;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_52 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_51, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_53, x_3, x_4, x_5, x_6, x_54);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_52, 0);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_52);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
case 8:
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_61 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(x_1, x_60, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_62, x_3, x_4, x_5, x_6, x_63);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 0);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_61);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
case 9:
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_70 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_1, x_69, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_71, x_3, x_4, x_5, x_6, x_72);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_73;
}
else
{
uint8_t x_74; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_70);
if (x_74 == 0)
{
return x_70;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_70, 0);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_70);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
case 10:
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_1, 1);
lean_inc(x_78);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_79 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_78, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_80, x_3, x_4, x_5, x_6, x_81);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_82;
}
else
{
uint8_t x_83; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_79);
if (x_83 == 0)
{
return x_79;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_79, 0);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_79);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
case 11:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_1, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_1, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 2);
lean_inc(x_89);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_90 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(x_87, x_88, x_89, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_91, x_3, x_4, x_5, x_6, x_92);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_93;
}
else
{
uint8_t x_94; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_90);
if (x_94 == 0)
{
return x_90;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_90, 0);
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_90);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
default: 
{
lean_object* x_98; 
lean_inc(x_1);
x_98 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_1, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 5);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 6);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 7);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 8);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 9);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 10);
lean_inc(x_17);
x_18 = lean_nat_dec_eq(x_10, x_11);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_20 = lean_ctor_get(x_4, 10);
lean_dec(x_20);
x_21 = lean_ctor_get(x_4, 9);
lean_dec(x_21);
x_22 = lean_ctor_get(x_4, 8);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 7);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 6);
lean_dec(x_24);
x_25 = lean_ctor_get(x_4, 5);
lean_dec(x_25);
x_26 = lean_ctor_get(x_4, 4);
lean_dec(x_26);
x_27 = lean_ctor_get(x_4, 3);
lean_dec(x_27);
x_28 = lean_ctor_get(x_4, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_4, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_4, 0);
lean_dec(x_30);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_10, x_31);
lean_dec(x_10);
lean_ctor_set(x_4, 3, x_32);
x_33 = lean_st_ref_get(x_5, x_6);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_st_ref_get(x_2, x_34);
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
x_40 = l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__7(x_39, x_1);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_free_object(x_35);
x_41 = lean_box(0);
x_42 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2(x_1, x_41, x_2, x_3, x_4, x_5, x_38);
return x_42;
}
else
{
lean_object* x_43; 
lean_dec(x_4);
lean_dec(x_5);
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
x_47 = l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__7(x_46, x_1);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_box(0);
x_49 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2(x_1, x_48, x_2, x_3, x_4, x_5, x_45);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_4);
lean_dec(x_5);
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
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_4);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_10, x_52);
lean_dec(x_10);
x_54 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_54, 0, x_7);
lean_ctor_set(x_54, 1, x_8);
lean_ctor_set(x_54, 2, x_9);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set(x_54, 4, x_11);
lean_ctor_set(x_54, 5, x_12);
lean_ctor_set(x_54, 6, x_13);
lean_ctor_set(x_54, 7, x_14);
lean_ctor_set(x_54, 8, x_15);
lean_ctor_set(x_54, 9, x_16);
lean_ctor_set(x_54, 10, x_17);
x_55 = lean_st_ref_get(x_5, x_6);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_st_ref_get(x_2, x_56);
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
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
lean_inc(x_1);
x_62 = l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__7(x_61, x_1);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
x_63 = lean_box(0);
x_64 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2(x_1, x_63, x_2, x_3, x_54, x_5, x_59);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_54);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
lean_dec(x_62);
if (lean_is_scalar(x_60)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_60;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_59);
return x_66;
}
}
}
else
{
lean_object* x_67; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_67 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10(x_12, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_67;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_expr_instantiate_rev(x_9, x_2);
lean_dec(x_9);
x_13 = lean_expr_instantiate_rev(x_10, x_2);
lean_dec(x_10);
x_47 = lean_st_ref_get(x_6, x_7);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_st_ref_get(x_3, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_box(0);
x_54 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
x_55 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_52);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_53);
lean_ctor_set(x_57, 4, x_56);
lean_ctor_set(x_57, 5, x_53);
x_58 = lean_st_ref_get(x_6, x_51);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__13;
x_61 = lean_st_mk_ref(x_60, x_59);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_62);
lean_inc(x_12);
x_64 = l_Lean_Meta_isProp(x_12, x_57, x_62, x_5, x_6, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_st_ref_get(x_6, x_66);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_st_ref_get(x_62, x_68);
lean_dec(x_62);
x_70 = lean_unbox(x_65);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_65);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_12);
x_72 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(x_12, x_3, x_4, x_5, x_6, x_71);
x_14 = x_72;
goto block_46;
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_69);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_69, 0);
lean_dec(x_74);
lean_ctor_set(x_69, 0, x_65);
x_14 = x_69;
goto block_46;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_dec(x_69);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_65);
lean_ctor_set(x_76, 1, x_75);
x_14 = x_76;
goto block_46;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_62);
x_77 = !lean_is_exclusive(x_64);
if (x_77 == 0)
{
x_14 = x_64;
goto block_46;
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
x_14 = x_80;
goto block_46;
}
}
block_46:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_12);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_12, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
x_21 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_13, x_3, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(x_8, x_12, x_13, x_19, x_22, x_3, x_4, x_5, x_6, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Expr_fvar___override(x_27);
x_29 = lean_array_push(x_2, x_28);
x_1 = x_11;
x_2 = x_29;
x_7 = x_26;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
uint8_t x_35; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_39; lean_object* x_40; 
lean_dec(x_12);
lean_dec(x_8);
x_39 = lean_ctor_get(x_14, 1);
lean_inc(x_39);
lean_dec(x_14);
x_40 = lean_array_push(x_2, x_13);
x_1 = x_11;
x_2 = x_40;
x_7 = x_39;
goto _start;
}
}
else
{
uint8_t x_42; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
return x_14;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
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
lean_object* x_81; lean_object* x_82; 
x_81 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_82 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_81, x_3, x_4, x_5, x_6, x_7);
return x_82;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lcErased", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_dec(x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(x_2, x_4, x_5, x_6, x_7, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_9, 0);
lean_dec(x_15);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__3;
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__3;
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_3, x_9);
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
x_21 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__13;
x_22 = lean_st_mk_ref(x_21, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_23);
lean_inc(x_1);
x_25 = lean_infer_type(x_1, x_18, x_23, x_5, x_6, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_6, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_get(x_23, x_29);
lean_dec(x_23);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_st_ref_get(x_6, x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_st_ref_get(x_3, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_15);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_16);
lean_ctor_set(x_38, 3, x_14);
lean_ctor_set(x_38, 4, x_17);
lean_ctor_set(x_38, 5, x_14);
x_39 = lean_st_ref_get(x_6, x_36);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_st_mk_ref(x_21, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_42);
lean_inc(x_26);
x_44 = l_Lean_Meta_isProp(x_26, x_38, x_42, x_5, x_6, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_st_ref_get(x_6, x_46);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_st_ref_get(x_42, x_48);
lean_dec(x_42);
x_50 = lean_unbox(x_45);
lean_dec(x_45);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_box(0);
x_53 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2(x_26, x_1, x_52, x_3, x_4, x_5, x_6, x_51);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
x_56 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__3;
lean_ctor_set(x_49, 0, x_56);
return x_49;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_49, 1);
lean_inc(x_57);
lean_dec(x_49);
x_58 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__3;
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_42);
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_44);
if (x_60 == 0)
{
return x_44;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_44, 0);
x_62 = lean_ctor_get(x_44, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_44);
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
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_25);
if (x_64 == 0)
{
return x_25;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_25, 0);
x_66 = lean_ctor_get(x_25, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_25);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 7);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 8);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 9);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 10);
lean_inc(x_18);
x_19 = lean_nat_dec_eq(x_11, x_12);
if (x_7 == 0)
{
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_4, 10);
lean_dec(x_21);
x_22 = lean_ctor_get(x_4, 9);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 8);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 7);
lean_dec(x_24);
x_25 = lean_ctor_get(x_4, 6);
lean_dec(x_25);
x_26 = lean_ctor_get(x_4, 5);
lean_dec(x_26);
x_27 = lean_ctor_get(x_4, 4);
lean_dec(x_27);
x_28 = lean_ctor_get(x_4, 3);
lean_dec(x_28);
x_29 = lean_ctor_get(x_4, 2);
lean_dec(x_29);
x_30 = lean_ctor_get(x_4, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_4, 0);
lean_dec(x_31);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_11, x_32);
lean_dec(x_11);
lean_ctor_set(x_4, 3, x_33);
x_34 = lean_box(0);
x_35 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__3(x_1, x_34, x_2, x_3, x_4, x_5, x_6);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_4);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_11, x_36);
lean_dec(x_11);
x_38 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_38, 0, x_8);
lean_ctor_set(x_38, 1, x_9);
lean_ctor_set(x_38, 2, x_10);
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set(x_38, 4, x_12);
lean_ctor_set(x_38, 5, x_13);
lean_ctor_set(x_38, 6, x_14);
lean_ctor_set(x_38, 7, x_15);
lean_ctor_set(x_38, 8, x_16);
lean_ctor_set(x_38, 9, x_17);
lean_ctor_set(x_38, 10, x_18);
x_39 = lean_box(0);
x_40 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__3(x_1, x_39, x_2, x_3, x_38, x_5, x_6);
return x_40;
}
}
else
{
lean_object* x_41; 
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
x_41 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10(x_13, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_41;
}
}
else
{
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
if (x_19 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__3;
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_6);
return x_43;
}
else
{
lean_object* x_44; 
x_44 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10(x_13, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_apply_6(x_2, x_9, x_3, x_4, x_5, x_6, x_10);
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
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 7, 0);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Compiler_LCNF_ToLCNF_toCode(x_10, x_2, x_3, x_4, x_5, x_11);
lean_dec(x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__2;
x_16 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_7, x_13, x_15, x_3, x_4, x_5, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_visitLambda___boxed), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___closed__1;
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 7, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___rarg(x_9, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_pushElement(x_13, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = l_Lean_Expr_fvar___override(x_17);
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
x_21 = l_Lean_Expr_fvar___override(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_proj___override(x_1, x_2, x_10);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__2;
x_14 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_12, x_13, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_array_set(x_2, x_3, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_3, x_12);
lean_dec(x_3);
x_1 = x_9;
x_2 = x_11;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault(x_16, x_2, x_4, x_5, x_6, x_7, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
static lean_object* _init_l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_projectionFnInfoExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_instInhabitedProjectionFunctionInfo;
x_12 = l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2___closed__1;
x_13 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_11, x_12, x_10, x_1);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_instInhabitedProjectionFunctionInfo;
x_18 = l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2___closed__1;
x_19 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_17, x_18, x_16, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_array_set(x_2, x_3, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_3, x_12);
lean_dec(x_3);
x_1 = x_9;
x_2 = x_11;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_15;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lift", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mk", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Eq", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("casesOn", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rec", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ndrec", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("And", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__17;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("False", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__20;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__21;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Empty", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__23;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__24;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__21;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__24;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_noConfusionExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5;
x_10 = lean_name_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7;
x_12 = lean_name_eq(x_8, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11;
x_14 = lean_name_eq(x_8, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13;
x_16 = lean_name_eq(x_8, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15;
x_18 = lean_name_eq(x_8, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__18;
x_20 = lean_name_eq(x_8, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__19;
x_22 = lean_name_eq(x_8, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__22;
x_24 = lean_name_eq(x_8, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__25;
x_26 = lean_name_eq(x_8, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__26;
x_28 = lean_name_eq(x_8, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__27;
x_30 = lean_name_eq(x_8, x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_8);
x_31 = l_Lean_Compiler_LCNF_getCasesInfo_x3f(x_8, x_4, x_5, x_6);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_8);
x_34 = l_Lean_Compiler_LCNF_getCtorArity_x3f(x_8, x_4, x_5, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_get(x_5, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__28;
lean_inc(x_8);
x_42 = l_Lean_TagDeclarationExtension_isTagged(x_41, x_40, x_8);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2(x_8, x_2, x_3, x_4, x_5, x_39);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_46);
x_48 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_47);
x_49 = lean_mk_array(x_47, x_48);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_sub(x_47, x_50);
lean_dec(x_47);
x_52 = l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__3(x_1, x_49, x_51, x_2, x_3, x_4, x_5, x_45);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
lean_dec(x_43);
x_54 = lean_ctor_get(x_44, 0);
lean_inc(x_54);
lean_dec(x_44);
x_55 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(x_54, x_1, x_2, x_3, x_4, x_5, x_53);
return x_55;
}
}
else
{
lean_object* x_56; 
lean_dec(x_8);
x_56 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion(x_1, x_2, x_3, x_4, x_5, x_39);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_8);
x_57 = lean_ctor_get(x_34, 1);
lean_inc(x_57);
lean_dec(x_34);
x_58 = lean_ctor_get(x_35, 0);
lean_inc(x_58);
lean_dec(x_35);
x_59 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(x_58, x_1, x_2, x_3, x_4, x_5, x_57);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_8);
x_64 = lean_ctor_get(x_31, 1);
lean_inc(x_64);
lean_dec(x_31);
x_65 = lean_ctor_get(x_32, 0);
lean_inc(x_65);
lean_dec(x_32);
x_66 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(x_65, x_1, x_2, x_3, x_4, x_5, x_64);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_31);
if (x_67 == 0)
{
return x_31;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_31, 0);
x_69 = lean_ctor_get(x_31, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_31);
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
lean_dec(x_8);
x_71 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6);
return x_71;
}
}
else
{
lean_object* x_72; 
lean_dec(x_8);
x_72 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6);
return x_72;
}
}
else
{
lean_object* x_73; 
lean_dec(x_8);
x_73 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6);
return x_73;
}
}
else
{
lean_object* x_74; 
lean_dec(x_8);
x_74 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6);
return x_74;
}
}
else
{
lean_object* x_75; 
lean_dec(x_8);
x_75 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndRec(x_1, x_2, x_3, x_4, x_5, x_6);
return x_75;
}
}
else
{
lean_object* x_76; 
lean_dec(x_8);
x_76 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndRec(x_1, x_2, x_3, x_4, x_5, x_6);
return x_76;
}
}
else
{
lean_object* x_77; 
lean_dec(x_8);
x_77 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6);
return x_77;
}
}
else
{
lean_object* x_78; 
lean_dec(x_8);
x_78 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_8);
x_79 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_8);
x_80 = lean_unsigned_to_nat(3u);
x_81 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(x_80, x_1, x_2, x_3, x_4, x_5, x_6);
return x_81;
}
}
else
{
lean_object* x_82; 
lean_dec(x_8);
x_82 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(x_1, x_2, x_3, x_4, x_5, x_6);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_7);
x_83 = lean_unsigned_to_nat(0u);
x_84 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_83);
x_85 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_84);
x_86 = lean_mk_array(x_84, x_85);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_sub(x_84, x_87);
lean_dec(x_84);
x_89 = l_Lean_Expr_withAppAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__1(x_1, x_86, x_88, x_2, x_3, x_4, x_5, x_6);
return x_89;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_13, x_2, x_15);
x_2 = x_18;
x_3 = x_19;
x_8 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__2;
x_9 = l_Lean_Expr_isConstOf(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault___spec__1(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_mkAppN(x_1, x_14);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__2;
x_18 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_16, x_17, x_3, x_4, x_5, x_6, x_15);
lean_dec(x_3);
return x_18;
}
else
{
uint8_t x_19; 
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_dec(x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(x_2, x_4, x_5, x_6, x_7, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_2, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_3, x_9);
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
x_21 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__13;
x_22 = lean_st_mk_ref(x_21, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_23);
lean_inc(x_1);
x_25 = lean_infer_type(x_1, x_18, x_23, x_5, x_6, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_6, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_get(x_23, x_29);
lean_dec(x_23);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_st_ref_get(x_6, x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_st_ref_get(x_3, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_15);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_16);
lean_ctor_set(x_38, 3, x_14);
lean_ctor_set(x_38, 4, x_17);
lean_ctor_set(x_38, 5, x_14);
x_39 = lean_st_ref_get(x_6, x_36);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_st_mk_ref(x_21, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_42);
lean_inc(x_26);
x_44 = l_Lean_Meta_isProp(x_26, x_38, x_42, x_5, x_6, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_st_ref_get(x_6, x_46);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_st_ref_get(x_42, x_48);
lean_dec(x_42);
x_50 = lean_unbox(x_45);
lean_dec(x_45);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_box(0);
x_53 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg___lambda__1(x_26, x_1, x_52, x_3, x_4, x_5, x_6, x_51);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
x_56 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__3;
lean_ctor_set(x_49, 0, x_56);
return x_49;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_49, 1);
lean_inc(x_57);
lean_dec(x_49);
x_58 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__3;
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_42);
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_44);
if (x_60 == 0)
{
return x_44;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_44, 0);
x_62 = lean_ctor_get(x_44, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_44);
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
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_25);
if (x_64 == 0)
{
return x_25;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_25, 0);
x_66 = lean_ctor_get(x_25, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_25);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg___lambda__2(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__3;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = lean_st_ref_get(x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_15);
x_17 = lean_ctor_get(x_4, 2);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__5;
lean_inc(x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_1);
lean_inc(x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_24);
x_26 = lean_ctor_get(x_4, 2);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__5;
lean_inc(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
x_29 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_1);
lean_inc(x_7);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
return x_31;
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_inc(x_1);
x_12 = lean_environment_find(x_11, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_7);
x_13 = lean_box(0);
x_14 = l_Lean_Expr_const___override(x_1, x_13);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__2(x_19, x_2, x_3, x_4, x_5, x_10);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_1);
x_25 = lean_environment_find(x_24, x_1);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_box(0);
x_27 = l_Lean_Expr_const___override(x_1, x_26);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___closed__4;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__2(x_32, x_2, x_3, x_4, x_5, x_23);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_23);
return x_35;
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
x_3 = lean_unsigned_to_nat(445u);
x_4 = lean_unsigned_to_nat(45u);
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = l_Lean_Name_getPrefix(x_8);
lean_dec(x_8);
x_10 = l_Lean_Compiler_LCNF_builtinRuntimeTypes;
x_11 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1(x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Core_instantiateValueLevelParams(x_16, x_14, x_5, x_6, x_17);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_21);
x_23 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_22);
x_24 = lean_mk_array(x_22, x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_22, x_25);
lean_dec(x_22);
x_27 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_24, x_26);
x_28 = l_Lean_Expr_beta(x_19, x_27);
x_29 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_28, x_3, x_4, x_5, x_6, x_20);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_12);
lean_dec(x_2);
x_34 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__2;
x_35 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_34, x_3, x_4, x_5, x_6, x_7);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_unsigned_to_nat(0u);
x_37 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_36);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_38, x_39);
lean_dec(x_38);
x_41 = lean_nat_dec_lt(x_37, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_40);
x_42 = l_Lean_Expr_getAppFn(x_2);
x_43 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_37);
x_44 = lean_mk_array(x_37, x_43);
x_45 = lean_nat_sub(x_37, x_39);
lean_dec(x_37);
x_46 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_44, x_45);
x_47 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault(x_42, x_46, x_3, x_4, x_5, x_6, x_7);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_nat_sub(x_40, x_37);
lean_dec(x_37);
lean_dec(x_40);
lean_inc(x_6);
lean_inc(x_5);
x_49 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(x_2, x_48, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_50, x_3, x_4, x_5, x_6, x_51);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_get_size(x_1);
x_10 = l_Array_toSubarray___rarg(x_1, x_2, x_9);
x_11 = l_Array_ofSubarray___rarg(x_10);
x_12 = l_Lean_mkAppN(x_3, x_11);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_add(x_1, x_13);
lean_dec(x_1);
x_15 = lean_nat_dec_lt(x_14, x_2);
x_16 = lean_st_ref_get(x_11, x_12);
if (x_15 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_14);
x_99 = lean_ctor_get(x_16, 1);
lean_inc(x_99);
lean_dec(x_16);
x_100 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_101 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_100);
x_17 = x_101;
x_18 = x_99;
goto block_98;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_16, 1);
lean_inc(x_102);
lean_dec(x_16);
x_103 = lean_array_fget(x_6, x_14);
lean_dec(x_14);
x_17 = x_103;
x_18 = x_102;
goto block_98;
}
block_98:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_19 = lean_st_ref_get(x_8, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__1;
x_25 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set(x_27, 5, x_23);
x_28 = lean_st_ref_get(x_11, x_21);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___closed__13;
x_31 = lean_st_mk_ref(x_30, x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_32);
x_34 = lean_whnf(x_17, x_27, x_32, x_10, x_11, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_get(x_11, x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_st_ref_get(x_32, x_38);
lean_dec(x_32);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_Expr_toCtorIfLit(x_7);
x_42 = l_Lean_Expr_toCtorIfLit(x_35);
x_43 = lean_st_ref_get(x_11, x_40);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_st_ref_get(x_11, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Expr_isConstructorApp_x3f(x_46, x_41);
lean_dec(x_41);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_50);
lean_dec(x_42);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_52 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_52, 0, x_3);
x_53 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__2;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__4;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6(x_56, x_8, x_9, x_10, x_11, x_49);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
lean_dec(x_51);
x_59 = l_Lean_Expr_isConstructorApp_x3f(x_50, x_42);
lean_dec(x_42);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_58);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_60 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_60, 0, x_3);
x_61 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__2;
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2___closed__4;
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6(x_64, x_8, x_9, x_10, x_11, x_49);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_dec(x_3);
x_66 = lean_ctor_get(x_59, 0);
lean_inc(x_66);
lean_dec(x_59);
x_67 = lean_ctor_get(x_58, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_name_eq(x_68, x_70);
lean_dec(x_70);
lean_dec(x_68);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_58);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_72 = l_Lean_Compiler_LCNF_inferType(x_4, x_9, x_10, x_11, x_49);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_73, x_8, x_9, x_10, x_11, x_74);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_75;
}
else
{
uint8_t x_76; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_76 = !lean_is_exclusive(x_72);
if (x_76 == 0)
{
return x_72;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_72, 0);
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_72);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_5, x_80);
x_82 = lean_nat_dec_lt(x_5, x_2);
lean_dec(x_2);
x_83 = lean_ctor_get(x_58, 4);
lean_inc(x_83);
lean_dec(x_58);
lean_inc(x_81);
lean_inc(x_6);
x_84 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__1), 8, 2);
lean_closure_set(x_84, 0, x_6);
lean_closure_set(x_84, 1, x_81);
if (x_82 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_6);
lean_dec(x_5);
x_85 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_86 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_85);
x_87 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___boxed), 7, 2);
lean_closure_set(x_87, 0, x_86);
lean_closure_set(x_87, 1, x_83);
x_88 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 7, 2);
lean_closure_set(x_88, 0, x_87);
lean_closure_set(x_88, 1, x_84);
x_89 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_4, x_81, x_88, x_8, x_9, x_10, x_11, x_49);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_array_fget(x_6, x_5);
lean_dec(x_5);
lean_dec(x_6);
x_91 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___boxed), 7, 2);
lean_closure_set(x_91, 0, x_90);
lean_closure_set(x_91, 1, x_83);
x_92 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 7, 2);
lean_closure_set(x_92, 0, x_91);
lean_closure_set(x_92, 1, x_84);
x_93 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_4, x_81, x_92, x_8, x_9, x_10, x_11, x_49);
return x_93;
}
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_32);
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
x_94 = !lean_is_exclusive(x_34);
if (x_94 == 0)
{
return x_34;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_34, 0);
x_96 = lean_ctor_get(x_34, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_34);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
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
x_3 = lean_unsigned_to_nat(402u);
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
x_3 = lean_unsigned_to_nat(404u);
x_4 = lean_unsigned_to_nat(56u);
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Name_getPrefix(x_8);
x_10 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1(x_9, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 5)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_nat_add(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_16, x_17);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_nat_add(x_18, x_19);
x_21 = lean_nat_add(x_20, x_17);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_22);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_23);
x_25 = lean_mk_array(x_23, x_24);
x_26 = lean_nat_sub(x_23, x_17);
lean_dec(x_23);
lean_inc(x_1);
x_27 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_25, x_26);
x_28 = lean_array_get_size(x_27);
x_29 = lean_nat_dec_lt(x_18, x_28);
lean_inc(x_27);
lean_inc(x_21);
lean_inc(x_1);
x_30 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lambda__2), 12, 6);
lean_closure_set(x_30, 0, x_16);
lean_closure_set(x_30, 1, x_28);
lean_closure_set(x_30, 2, x_8);
lean_closure_set(x_30, 3, x_1);
lean_closure_set(x_30, 4, x_21);
lean_closure_set(x_30, 5, x_27);
if (x_29 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
lean_dec(x_18);
x_31 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_32 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_31);
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_whnf___boxed), 6, 1);
lean_closure_set(x_33, 0, x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___boxed), 6, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 7, 2);
lean_closure_set(x_35, 0, x_34);
lean_closure_set(x_35, 1, x_30);
x_36 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_21, x_35, x_2, x_3, x_4, x_5, x_12);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_array_fget(x_27, x_18);
lean_dec(x_18);
lean_dec(x_27);
x_38 = lean_alloc_closure((void*)(l_Lean_Meta_whnf___boxed), 6, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___boxed), 6, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 7, 2);
lean_closure_set(x_40, 0, x_39);
lean_closure_set(x_40, 1, x_30);
x_41 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_21, x_40, x_2, x_3, x_4, x_5, x_12);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_1);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_dec(x_10);
x_43 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__3;
x_44 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_43, x_2, x_3, x_4, x_5, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_7);
lean_dec(x_1);
x_49 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__2;
x_50 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_49, x_2, x_3, x_4, x_5, x_6);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_9);
x_11 = lean_nat_dec_lt(x_10, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_apply_5(x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_nat_sub(x_2, x_10);
lean_dec(x_10);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(x_1, x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_15, x_4, x_5, x_6, x_7, x_16);
return x_17;
}
else
{
uint8_t x_18; 
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_array_push(x_4, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_5, x_4);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_26; uint8_t x_27; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_3, x_16);
lean_dec(x_3);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_7);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_26, 1);
x_31 = lean_ctor_get(x_7, 1);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_7);
x_18 = x_33;
x_19 = x_12;
goto block_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_26, 1, x_36);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_7);
x_18 = x_37;
x_19 = x_12;
goto block_25;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_26, 1);
x_39 = lean_ctor_get(x_7, 0);
lean_inc(x_39);
lean_dec(x_7);
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
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_26, 1, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_26);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_18 = x_45;
x_19 = x_12;
goto block_25;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_7);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_26, 1);
x_48 = lean_ctor_get(x_7, 0);
x_49 = lean_ctor_get(x_7, 1);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_51 = lean_ctor_get(x_47, 0);
x_52 = lean_ctor_get(x_47, 1);
x_53 = lean_ctor_get(x_28, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_28, 1);
lean_inc(x_54);
lean_dec(x_28);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_48, 2);
lean_inc(x_57);
x_58 = lean_nat_dec_lt(x_56, x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_53);
lean_ctor_set(x_26, 0, x_54);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_7);
x_18 = x_59;
x_19 = x_12;
goto block_25;
}
else
{
uint8_t x_60; 
lean_free_object(x_47);
lean_free_object(x_7);
lean_free_object(x_26);
x_60 = !lean_is_exclusive(x_48);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_48, 2);
lean_dec(x_61);
x_62 = lean_ctor_get(x_48, 1);
lean_dec(x_62);
x_63 = lean_ctor_get(x_48, 0);
lean_dec(x_63);
x_64 = lean_array_fget(x_55, x_56);
x_65 = lean_nat_add(x_56, x_16);
lean_dec(x_56);
lean_ctor_set(x_48, 1, x_65);
x_66 = lean_nat_dec_lt(x_4, x_2);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_68 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_67);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_69 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_53, x_64, x_68, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
lean_inc(x_52);
x_74 = l_Lean_Compiler_LCNF_compatibleTypes(x_72, x_52);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_52);
x_75 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_76 = lean_box(0);
x_77 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_73, x_54, x_48, x_51, x_75, x_76, x_8, x_9, x_10, x_11, x_71);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_18 = x_78;
x_19 = x_79;
goto block_25;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_box(0);
x_81 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_73, x_54, x_48, x_51, x_52, x_80, x_8, x_9, x_10, x_11, x_71);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_18 = x_82;
x_19 = x_83;
goto block_25;
}
}
else
{
uint8_t x_84; 
lean_dec(x_48);
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_84 = !lean_is_exclusive(x_69);
if (x_84 == 0)
{
return x_69;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_69, 0);
x_86 = lean_ctor_get(x_69, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_69);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_array_fget(x_1, x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_89 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_53, x_64, x_88, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
lean_inc(x_52);
x_94 = l_Lean_Compiler_LCNF_compatibleTypes(x_92, x_52);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_52);
x_95 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_96 = lean_box(0);
x_97 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_93, x_54, x_48, x_51, x_95, x_96, x_8, x_9, x_10, x_11, x_91);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_18 = x_98;
x_19 = x_99;
goto block_25;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_box(0);
x_101 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_93, x_54, x_48, x_51, x_52, x_100, x_8, x_9, x_10, x_11, x_91);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_18 = x_102;
x_19 = x_103;
goto block_25;
}
}
else
{
uint8_t x_104; 
lean_dec(x_48);
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_104 = !lean_is_exclusive(x_89);
if (x_104 == 0)
{
return x_89;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_89, 0);
x_106 = lean_ctor_get(x_89, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_89);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
lean_dec(x_48);
x_108 = lean_array_fget(x_55, x_56);
x_109 = lean_nat_add(x_56, x_16);
lean_dec(x_56);
x_110 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_110, 0, x_55);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_110, 2, x_57);
x_111 = lean_nat_dec_lt(x_4, x_2);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_113 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_112);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_114 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_53, x_108, x_113, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
lean_inc(x_52);
x_119 = l_Lean_Compiler_LCNF_compatibleTypes(x_117, x_52);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_52);
x_120 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_121 = lean_box(0);
x_122 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_118, x_54, x_110, x_51, x_120, x_121, x_8, x_9, x_10, x_11, x_116);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_18 = x_123;
x_19 = x_124;
goto block_25;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_box(0);
x_126 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_118, x_54, x_110, x_51, x_52, x_125, x_8, x_9, x_10, x_11, x_116);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_18 = x_127;
x_19 = x_128;
goto block_25;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_110);
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_129 = lean_ctor_get(x_114, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_114, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_131 = x_114;
} else {
 lean_dec_ref(x_114);
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
lean_object* x_133; lean_object* x_134; 
x_133 = lean_array_fget(x_1, x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_134 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_53, x_108, x_133, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
lean_inc(x_52);
x_139 = l_Lean_Compiler_LCNF_compatibleTypes(x_137, x_52);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_52);
x_140 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_141 = lean_box(0);
x_142 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_138, x_54, x_110, x_51, x_140, x_141, x_8, x_9, x_10, x_11, x_136);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_18 = x_143;
x_19 = x_144;
goto block_25;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_box(0);
x_146 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_138, x_54, x_110, x_51, x_52, x_145, x_8, x_9, x_10, x_11, x_136);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_18 = x_147;
x_19 = x_148;
goto block_25;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_110);
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_149 = lean_ctor_get(x_134, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_134, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_151 = x_134;
} else {
 lean_dec_ref(x_134);
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
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_153 = lean_ctor_get(x_47, 0);
x_154 = lean_ctor_get(x_47, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_47);
x_155 = lean_ctor_get(x_28, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_28, 1);
lean_inc(x_156);
lean_dec(x_28);
x_157 = lean_ctor_get(x_48, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_48, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_48, 2);
lean_inc(x_159);
x_160 = lean_nat_dec_lt(x_158, x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_155);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_153);
lean_ctor_set(x_161, 1, x_154);
lean_ctor_set(x_26, 1, x_161);
lean_ctor_set(x_26, 0, x_156);
x_162 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_162, 0, x_7);
x_18 = x_162;
x_19 = x_12;
goto block_25;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
lean_free_object(x_7);
lean_free_object(x_26);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 x_163 = x_48;
} else {
 lean_dec_ref(x_48);
 x_163 = lean_box(0);
}
x_164 = lean_array_fget(x_157, x_158);
x_165 = lean_nat_add(x_158, x_16);
lean_dec(x_158);
if (lean_is_scalar(x_163)) {
 x_166 = lean_alloc_ctor(0, 3, 0);
} else {
 x_166 = x_163;
}
lean_ctor_set(x_166, 0, x_157);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set(x_166, 2, x_159);
x_167 = lean_nat_dec_lt(x_4, x_2);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_169 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_168);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_170 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_155, x_164, x_169, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
lean_inc(x_154);
x_175 = l_Lean_Compiler_LCNF_compatibleTypes(x_173, x_154);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_154);
x_176 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_177 = lean_box(0);
x_178 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_174, x_156, x_166, x_153, x_176, x_177, x_8, x_9, x_10, x_11, x_172);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_18 = x_179;
x_19 = x_180;
goto block_25;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_box(0);
x_182 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_174, x_156, x_166, x_153, x_154, x_181, x_8, x_9, x_10, x_11, x_172);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_18 = x_183;
x_19 = x_184;
goto block_25;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_166);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_185 = lean_ctor_get(x_170, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_170, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_187 = x_170;
} else {
 lean_dec_ref(x_170);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_array_fget(x_1, x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_190 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_155, x_164, x_189, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
lean_dec(x_191);
lean_inc(x_154);
x_195 = l_Lean_Compiler_LCNF_compatibleTypes(x_193, x_154);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_154);
x_196 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_197 = lean_box(0);
x_198 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_194, x_156, x_166, x_153, x_196, x_197, x_8, x_9, x_10, x_11, x_192);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_18 = x_199;
x_19 = x_200;
goto block_25;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_201 = lean_box(0);
x_202 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_194, x_156, x_166, x_153, x_154, x_201, x_8, x_9, x_10, x_11, x_192);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_18 = x_203;
x_19 = x_204;
goto block_25;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_166);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_205 = lean_ctor_get(x_190, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_190, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_207 = x_190;
} else {
 lean_dec_ref(x_190);
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
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_209 = lean_ctor_get(x_26, 1);
x_210 = lean_ctor_get(x_7, 0);
lean_inc(x_210);
lean_dec(x_7);
x_211 = lean_ctor_get(x_209, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_213 = x_209;
} else {
 lean_dec_ref(x_209);
 x_213 = lean_box(0);
}
x_214 = lean_ctor_get(x_28, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_28, 1);
lean_inc(x_215);
lean_dec(x_28);
x_216 = lean_ctor_get(x_210, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_210, 1);
lean_inc(x_217);
x_218 = lean_ctor_get(x_210, 2);
lean_inc(x_218);
x_219 = lean_nat_dec_lt(x_217, x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_214);
if (lean_is_scalar(x_213)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_213;
}
lean_ctor_set(x_220, 0, x_211);
lean_ctor_set(x_220, 1, x_212);
lean_ctor_set(x_26, 1, x_220);
lean_ctor_set(x_26, 0, x_215);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_210);
lean_ctor_set(x_221, 1, x_26);
x_222 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_222, 0, x_221);
x_18 = x_222;
x_19 = x_12;
goto block_25;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
lean_dec(x_213);
lean_free_object(x_26);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 x_223 = x_210;
} else {
 lean_dec_ref(x_210);
 x_223 = lean_box(0);
}
x_224 = lean_array_fget(x_216, x_217);
x_225 = lean_nat_add(x_217, x_16);
lean_dec(x_217);
if (lean_is_scalar(x_223)) {
 x_226 = lean_alloc_ctor(0, 3, 0);
} else {
 x_226 = x_223;
}
lean_ctor_set(x_226, 0, x_216);
lean_ctor_set(x_226, 1, x_225);
lean_ctor_set(x_226, 2, x_218);
x_227 = lean_nat_dec_lt(x_4, x_2);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_229 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_228);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_230 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_214, x_224, x_229, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_ctor_get(x_231, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_231, 1);
lean_inc(x_234);
lean_dec(x_231);
lean_inc(x_212);
x_235 = l_Lean_Compiler_LCNF_compatibleTypes(x_233, x_212);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_212);
x_236 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_237 = lean_box(0);
x_238 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_234, x_215, x_226, x_211, x_236, x_237, x_8, x_9, x_10, x_11, x_232);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_18 = x_239;
x_19 = x_240;
goto block_25;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_241 = lean_box(0);
x_242 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_234, x_215, x_226, x_211, x_212, x_241, x_8, x_9, x_10, x_11, x_232);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_18 = x_243;
x_19 = x_244;
goto block_25;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_226);
lean_dec(x_215);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_245 = lean_ctor_get(x_230, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_230, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_247 = x_230;
} else {
 lean_dec_ref(x_230);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_array_fget(x_1, x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_250 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_214, x_224, x_249, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_ctor_get(x_251, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
lean_dec(x_251);
lean_inc(x_212);
x_255 = l_Lean_Compiler_LCNF_compatibleTypes(x_253, x_212);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_212);
x_256 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_257 = lean_box(0);
x_258 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_254, x_215, x_226, x_211, x_256, x_257, x_8, x_9, x_10, x_11, x_252);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_18 = x_259;
x_19 = x_260;
goto block_25;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_box(0);
x_262 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_254, x_215, x_226, x_211, x_212, x_261, x_8, x_9, x_10, x_11, x_252);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_18 = x_263;
x_19 = x_264;
goto block_25;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_226);
lean_dec(x_215);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_265 = lean_ctor_get(x_250, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_250, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_267 = x_250;
} else {
 lean_dec_ref(x_250);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(1, 2, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_265);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
}
}
}
}
}
else
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_26, 1);
x_270 = lean_ctor_get(x_26, 0);
lean_inc(x_269);
lean_inc(x_270);
lean_dec(x_26);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_271 = lean_ctor_get(x_7, 0);
lean_inc(x_271);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_272 = x_7;
} else {
 lean_dec_ref(x_7);
 x_272 = lean_box(0);
}
x_273 = lean_ctor_get(x_269, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_269, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_275 = x_269;
} else {
 lean_dec_ref(x_269);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_270);
lean_ctor_set(x_277, 1, x_276);
if (lean_is_scalar(x_272)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_272;
}
lean_ctor_set(x_278, 0, x_271);
lean_ctor_set(x_278, 1, x_277);
x_279 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_279, 0, x_278);
x_18 = x_279;
x_19 = x_12;
goto block_25;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_280 = lean_ctor_get(x_7, 0);
lean_inc(x_280);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_281 = x_7;
} else {
 lean_dec_ref(x_7);
 x_281 = lean_box(0);
}
x_282 = lean_ctor_get(x_269, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_269, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_284 = x_269;
} else {
 lean_dec_ref(x_269);
 x_284 = lean_box(0);
}
x_285 = lean_ctor_get(x_270, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_270, 1);
lean_inc(x_286);
lean_dec(x_270);
x_287 = lean_ctor_get(x_280, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_280, 1);
lean_inc(x_288);
x_289 = lean_ctor_get(x_280, 2);
lean_inc(x_289);
x_290 = lean_nat_dec_lt(x_288, x_289);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_285);
if (lean_is_scalar(x_284)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_284;
}
lean_ctor_set(x_291, 0, x_282);
lean_ctor_set(x_291, 1, x_283);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_286);
lean_ctor_set(x_292, 1, x_291);
if (lean_is_scalar(x_281)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_281;
}
lean_ctor_set(x_293, 0, x_280);
lean_ctor_set(x_293, 1, x_292);
x_294 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_294, 0, x_293);
x_18 = x_294;
x_19 = x_12;
goto block_25;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
lean_dec(x_284);
lean_dec(x_281);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 lean_ctor_release(x_280, 2);
 x_295 = x_280;
} else {
 lean_dec_ref(x_280);
 x_295 = lean_box(0);
}
x_296 = lean_array_fget(x_287, x_288);
x_297 = lean_nat_add(x_288, x_16);
lean_dec(x_288);
if (lean_is_scalar(x_295)) {
 x_298 = lean_alloc_ctor(0, 3, 0);
} else {
 x_298 = x_295;
}
lean_ctor_set(x_298, 0, x_287);
lean_ctor_set(x_298, 1, x_297);
lean_ctor_set(x_298, 2, x_289);
x_299 = lean_nat_dec_lt(x_4, x_2);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_301 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_300);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_302 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_285, x_296, x_301, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec(x_302);
x_305 = lean_ctor_get(x_303, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_303, 1);
lean_inc(x_306);
lean_dec(x_303);
lean_inc(x_283);
x_307 = l_Lean_Compiler_LCNF_compatibleTypes(x_305, x_283);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_283);
x_308 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_309 = lean_box(0);
x_310 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_306, x_286, x_298, x_282, x_308, x_309, x_8, x_9, x_10, x_11, x_304);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
x_18 = x_311;
x_19 = x_312;
goto block_25;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_313 = lean_box(0);
x_314 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_306, x_286, x_298, x_282, x_283, x_313, x_8, x_9, x_10, x_11, x_304);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
x_18 = x_315;
x_19 = x_316;
goto block_25;
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_298);
lean_dec(x_286);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_317 = lean_ctor_get(x_302, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_302, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_319 = x_302;
} else {
 lean_dec_ref(x_302);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 2, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_318);
return x_320;
}
}
else
{
lean_object* x_321; lean_object* x_322; 
x_321 = lean_array_fget(x_1, x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_322 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_285, x_296, x_321, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec(x_322);
x_325 = lean_ctor_get(x_323, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_323, 1);
lean_inc(x_326);
lean_dec(x_323);
lean_inc(x_283);
x_327 = l_Lean_Compiler_LCNF_compatibleTypes(x_325, x_283);
if (x_327 == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_283);
x_328 = l_Lean_Compiler_LCNF_anyTypeExpr;
x_329 = lean_box(0);
x_330 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_326, x_286, x_298, x_282, x_328, x_329, x_8, x_9, x_10, x_11, x_324);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_18 = x_331;
x_19 = x_332;
goto block_25;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_333 = lean_box(0);
x_334 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_326, x_286, x_298, x_282, x_283, x_333, x_8, x_9, x_10, x_11, x_324);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec(x_334);
x_18 = x_335;
x_19 = x_336;
goto block_25;
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_298);
lean_dec(x_286);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_337 = lean_ctor_get(x_322, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_322, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 x_339 = x_322;
} else {
 lean_dec_ref(x_322);
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
}
block_25:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_17;
x_4 = x_23;
x_7 = x_22;
x_12 = x_19;
goto _start;
}
}
}
else
{
lean_object* x_341; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_7);
lean_ctor_set(x_341, 1, x_12);
return x_341;
}
}
else
{
lean_object* x_342; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_7);
lean_ctor_set(x_342, 1, x_12);
return x_342;
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
x_3 = lean_unsigned_to_nat(336u);
x_4 = lean_unsigned_to_nat(55u);
x_5 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
x_12 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_79; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
x_16 = lean_array_get_size(x_2);
x_79 = lean_nat_dec_lt(x_15, x_16);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_15);
x_80 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_81 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_80);
x_17 = x_81;
goto block_78;
}
else
{
lean_object* x_82; 
x_82 = lean_array_fget(x_2, x_15);
lean_dec(x_15);
x_17 = x_82;
goto block_78;
}
block_78:
{
lean_object* x_18; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_17, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_3);
x_21 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1(x_3, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 5)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_1, 5);
lean_inc(x_25);
x_26 = lean_array_get_size(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Array_toSubarray___rarg(x_25, x_27, x_26);
x_29 = lean_ctor_get(x_24, 4);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_ctor_get(x_1, 4);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_13);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 2);
lean_inc(x_36);
lean_dec(x_30);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_34);
x_37 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1(x_2, x_16, x_34, x_35, x_34, x_36, x_33, x_7, x_8, x_9, x_10, x_23);
lean_dec(x_36);
lean_dec(x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = l_Lean_Expr_fvarId_x21(x_19);
lean_inc(x_43);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_3);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_42);
x_46 = l_Lean_Compiler_LCNF_mkAuxParam(x_43, x_8, x_9, x_10, x_41);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_49);
x_50 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
x_51 = l_Lean_Compiler_LCNF_ToLCNF_pushElement(x_50, x_7, x_8, x_9, x_10, x_48);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_51, 1);
x_54 = lean_ctor_get(x_51, 0);
lean_dec(x_54);
x_55 = l_Lean_Expr_fvar___override(x_49);
x_56 = lean_nat_dec_eq(x_16, x_5);
lean_dec(x_16);
if (x_56 == 0)
{
lean_object* x_57; 
lean_free_object(x_51);
x_57 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_55, x_2, x_5, x_7, x_8, x_9, x_10, x_53);
return x_57;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_ctor_set(x_51, 0, x_55);
return x_51;
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_dec(x_51);
x_59 = l_Lean_Expr_fvar___override(x_49);
x_60 = lean_nat_dec_eq(x_16, x_5);
lean_dec(x_16);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_59, x_2, x_5, x_7, x_8, x_9, x_10, x_58);
return x_61;
}
else
{
lean_object* x_62; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_58);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_37);
if (x_63 == 0)
{
return x_37;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_37, 0);
x_65 = lean_ctor_get(x_37, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_37);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = lean_ctor_get(x_21, 1);
lean_inc(x_67);
lean_dec(x_21);
x_68 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1___closed__2;
x_69 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_68, x_7, x_8, x_9, x_10, x_67);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_21);
if (x_70 == 0)
{
return x_21;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_21, 0);
x_72 = lean_ctor_get(x_21, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_21);
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
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_18);
if (x_74 == 0)
{
return x_18;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_18, 0);
x_76 = lean_ctor_get(x_18, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_18);
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
uint8_t x_83; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_12);
if (x_83 == 0)
{
return x_12;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_12, 0);
x_85 = lean_ctor_get(x_12, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_12);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_9);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_10);
x_12 = lean_mk_array(x_10, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_10, x_13);
lean_dec(x_10);
lean_inc(x_2);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_12, x_14);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = l_Lean_Name_getPrefix(x_16);
lean_dec(x_16);
x_18 = l_Lean_Expr_getAppFn(x_2);
lean_inc(x_8);
lean_inc(x_15);
x_19 = l_Array_toSubarray___rarg(x_15, x_9, x_8);
x_20 = l_Array_ofSubarray___rarg(x_19);
x_21 = l_Lean_mkAppN(x_18, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___boxed), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement___closed__1;
lean_inc(x_8);
x_25 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lambda__1), 11, 5);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_15);
lean_closure_set(x_25, 2, x_17);
lean_closure_set(x_25, 3, x_24);
lean_closure_set(x_25, 4, x_8);
x_26 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 7, 2);
lean_closure_set(x_26, 0, x_23);
lean_closure_set(x_26, 1, x_25);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_2, x_8, x_26, x_3, x_4, x_5, x_6, x_7);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_1, x_14);
lean_dec(x_1);
x_16 = lean_array_get_size(x_5);
x_17 = lean_nat_dec_lt(x_2, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_array_fget(x_5, x_2);
x_21 = lean_box(0);
x_22 = lean_array_fset(x_5, x_2, x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_23 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_20, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_array_fset(x_22, x_2, x_24);
x_27 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_27;
x_5 = x_26;
x_10 = x_25;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
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
}
else
{
lean_object* x_33; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_10);
return x_33;
}
}
else
{
lean_object* x_34; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_10);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_eq(x_9, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_1, x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(1u);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_16 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___spec__1(x_9, x_3, x_9, x_15, x_2, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_get_size(x_17);
x_20 = l_Array_toSubarray___rarg(x_17, x_3, x_19);
x_21 = l_Array_ofSubarray___rarg(x_20);
x_22 = l_Lean_mkAppN(x_13, x_21);
x_23 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_22, x_11, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_4);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
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
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_32 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__2;
x_33 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_1, x_32, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_2, x_5, x_6, x_7, x_8, x_9);
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
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toCode(x_11, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_inferType(x_2, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_19, 2, x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
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
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set(x_23, 2, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_13);
if (x_30 == 0)
{
return x_13;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_10);
if (x_34 == 0)
{
return x_10;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_10, 0);
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_10);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_array_get_size(x_9);
x_12 = lean_nat_dec_lt(x_11, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__1(x_1, x_10, x_9, x_13, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_nat_sub(x_2, x_11);
lean_dec(x_11);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(x_10, x_15, x_4, x_5, x_6, x_7, x_8);
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
x_19 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda(x_17, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Array_append___rarg(x_9, x_22);
x_25 = lean_box(0);
x_26 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__1(x_1, x_23, x_24, x_25, x_4, x_5, x_6, x_7, x_21);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___boxed), 7, 2);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__2), 8, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 7, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___rarg(x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
x_7 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_8, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
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
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___boxed), 6, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___closed__1;
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 7, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_11, x_10, x_2, x_3, x_4, x_5, x_6);
return x_12;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_7);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_8);
x_10 = lean_mk_array(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_8, x_11);
lean_dec(x_8);
lean_inc(x_1);
x_13 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_10, x_12);
x_14 = lean_array_get_size(x_13);
x_15 = lean_nat_dec_lt(x_7, x_14);
x_16 = lean_nat_dec_lt(x_11, x_14);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__18;
x_18 = l_Lean_Expr_isAppOf(x_1, x_17);
x_19 = lean_array_get_size(x_13);
x_20 = lean_unsigned_to_nat(5u);
lean_inc(x_13);
x_21 = l_Array_toSubarray___rarg(x_13, x_20, x_19);
x_22 = l_Array_ofSubarray___rarg(x_21);
if (x_15 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_62 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_61);
x_23 = x_62;
goto block_60;
}
else
{
lean_object* x_63; 
x_63 = lean_array_fget(x_13, x_7);
x_23 = x_63;
goto block_60;
}
block_60:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(x_23);
x_25 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndRec___closed__1;
x_26 = lean_array_push(x_25, x_24);
if (x_16 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_58 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_57);
x_27 = x_58;
goto block_56;
}
else
{
lean_object* x_59; 
x_59 = lean_array_fget(x_13, x_11);
x_27 = x_59;
goto block_56;
}
block_56:
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(x_27);
x_29 = lean_array_push(x_26, x_28);
if (x_18 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_unsigned_to_nat(4u);
x_31 = lean_nat_dec_lt(x_30, x_14);
lean_dec(x_14);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_13);
x_32 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_33 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_32);
x_34 = l_Lean_Expr_beta(x_33, x_29);
x_35 = l_Lean_mkAppN(x_34, x_22);
x_36 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 6, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_20, x_36, x_2, x_3, x_4, x_5, x_6);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_array_fget(x_13, x_30);
lean_dec(x_13);
x_39 = l_Lean_Expr_beta(x_38, x_29);
x_40 = l_Lean_mkAppN(x_39, x_22);
x_41 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 6, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_20, x_41, x_2, x_3, x_4, x_5, x_6);
return x_42;
}
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_unsigned_to_nat(3u);
x_44 = lean_nat_dec_lt(x_43, x_14);
lean_dec(x_14);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_13);
x_45 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_46 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_45);
x_47 = l_Lean_Expr_beta(x_46, x_29);
x_48 = l_Lean_mkAppN(x_47, x_22);
x_49 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 6, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_20, x_49, x_2, x_3, x_4, x_5, x_6);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_array_fget(x_13, x_43);
lean_dec(x_13);
x_52 = l_Lean_Expr_beta(x_51, x_29);
x_53 = l_Lean_mkAppN(x_52, x_22);
x_54 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 6, 1);
lean_closure_set(x_54, 0, x_53);
x_55 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_20, x_54, x_2, x_3, x_4, x_5, x_6);
return x_55;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(6u);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_2, x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_88; uint8_t x_89; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_88 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13;
x_89 = l_Lean_Expr_isAppOf(x_2, x_88);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__15;
x_91 = l_Lean_Expr_isAppOf(x_2, x_90);
lean_dec(x_2);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_array_get_size(x_1);
x_93 = lean_unsigned_to_nat(5u);
x_94 = lean_nat_dec_lt(x_93, x_92);
lean_dec(x_92);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_96 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_95);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_97 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_96, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_98);
x_100 = l_Lean_Compiler_LCNF_inferType(x_98, x_5, x_6, x_7, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_10);
x_103 = l_Lean_Compiler_LCNF_compatibleTypes(x_101, x_10);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_105 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_98, x_104, x_4, x_5, x_6, x_7, x_102);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_108 = l_Lean_Compiler_LCNF_mkLcCast(x_106, x_10, x_5, x_6, x_7, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_unsigned_to_nat(6u);
x_112 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_109, x_1, x_111, x_4, x_5, x_6, x_7, x_110);
return x_112;
}
else
{
uint8_t x_113; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
else
{
uint8_t x_117; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_105);
if (x_117 == 0)
{
return x_105;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_105, 0);
x_119 = lean_ctor_get(x_105, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_105);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_10);
x_121 = lean_unsigned_to_nat(6u);
x_122 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_98, x_1, x_121, x_4, x_5, x_6, x_7, x_102);
return x_122;
}
}
else
{
uint8_t x_123; 
lean_dec(x_98);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_100);
if (x_123 == 0)
{
return x_100;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_100, 0);
x_125 = lean_ctor_get(x_100, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_100);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_97);
if (x_127 == 0)
{
return x_97;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_97, 0);
x_129 = lean_ctor_get(x_97, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_97);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_array_fget(x_1, x_93);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_132 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_131, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_133);
x_135 = l_Lean_Compiler_LCNF_inferType(x_133, x_5, x_6, x_7, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
lean_inc(x_10);
x_138 = l_Lean_Compiler_LCNF_compatibleTypes(x_136, x_10);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_140 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_133, x_139, x_4, x_5, x_6, x_7, x_137);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_143 = l_Lean_Compiler_LCNF_mkLcCast(x_141, x_10, x_5, x_6, x_7, x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_unsigned_to_nat(6u);
x_147 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_144, x_1, x_146, x_4, x_5, x_6, x_7, x_145);
return x_147;
}
else
{
uint8_t x_148; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_143);
if (x_148 == 0)
{
return x_143;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_143, 0);
x_150 = lean_ctor_get(x_143, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_143);
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
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_140);
if (x_152 == 0)
{
return x_140;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_140, 0);
x_154 = lean_ctor_get(x_140, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_140);
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
lean_dec(x_10);
x_156 = lean_unsigned_to_nat(6u);
x_157 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_133, x_1, x_156, x_4, x_5, x_6, x_7, x_137);
return x_157;
}
}
else
{
uint8_t x_158; 
lean_dec(x_133);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_135);
if (x_158 == 0)
{
return x_135;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_135, 0);
x_160 = lean_ctor_get(x_135, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_135);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_162 = !lean_is_exclusive(x_132);
if (x_162 == 0)
{
return x_132;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_132, 0);
x_164 = lean_ctor_get(x_132, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_132);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
}
else
{
lean_object* x_166; 
x_166 = lean_box(0);
x_12 = x_166;
goto block_87;
}
}
else
{
lean_object* x_167; 
lean_dec(x_2);
x_167 = lean_box(0);
x_12 = x_167;
goto block_87;
}
block_87:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_12);
x_13 = lean_array_get_size(x_1);
x_14 = lean_unsigned_to_nat(3u);
x_15 = lean_nat_dec_lt(x_14, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_17 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_17, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_19);
x_21 = l_Lean_Compiler_LCNF_inferType(x_19, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_10);
x_24 = l_Lean_Compiler_LCNF_compatibleTypes(x_22, x_10);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_26 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_19, x_25, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = l_Lean_Compiler_LCNF_mkLcCast(x_27, x_10, x_5, x_6, x_7, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(6u);
x_33 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_30, x_1, x_32, x_4, x_5, x_6, x_7, x_31);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
return x_26;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_26, 0);
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_26);
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
lean_dec(x_10);
x_42 = lean_unsigned_to_nat(6u);
x_43 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_19, x_1, x_42, x_4, x_5, x_6, x_7, x_23);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_21);
if (x_44 == 0)
{
return x_21;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_21, 0);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_21);
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
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_18);
if (x_48 == 0)
{
return x_18;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_18, 0);
x_50 = lean_ctor_get(x_18, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_18);
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
x_52 = lean_array_fget(x_1, x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_53 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_52, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_54);
x_56 = l_Lean_Compiler_LCNF_inferType(x_54, x_5, x_6, x_7, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_10);
x_59 = l_Lean_Compiler_LCNF_compatibleTypes(x_57, x_10);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_61 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_54, x_60, x_4, x_5, x_6, x_7, x_58);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_64 = l_Lean_Compiler_LCNF_mkLcCast(x_62, x_10, x_5, x_6, x_7, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_unsigned_to_nat(6u);
x_68 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_65, x_1, x_67, x_4, x_5, x_6, x_7, x_66);
return x_68;
}
else
{
uint8_t x_69; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_61);
if (x_73 == 0)
{
return x_61;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_61, 0);
x_75 = lean_ctor_get(x_61, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_61);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_10);
x_77 = lean_unsigned_to_nat(6u);
x_78 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_54, x_1, x_77, x_4, x_5, x_6, x_7, x_58);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec(x_54);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_56);
if (x_79 == 0)
{
return x_56;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_56, 0);
x_81 = lean_ctor_get(x_56, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_56);
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
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_53);
if (x_83 == 0)
{
return x_53;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_53, 0);
x_85 = lean_ctor_get(x_53, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_53);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_168 = !lean_is_exclusive(x_9);
if (x_168 == 0)
{
return x_9;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_9, 0);
x_170 = lean_ctor_get(x_9, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_9);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_7);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_8);
x_10 = lean_mk_array(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_8, x_11);
lean_dec(x_8);
lean_inc(x_1);
x_13 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_10, x_12);
x_14 = l_Lean_Expr_getAppFn(x_1);
x_15 = lean_unsigned_to_nat(6u);
lean_inc(x_13);
x_16 = l_Array_toSubarray___rarg(x_13, x_7, x_15);
x_17 = l_Array_ofSubarray___rarg(x_16);
x_18 = l_Lean_mkAppN(x_14, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___rarg___boxed), 6, 1);
lean_closure_set(x_20, 0, x_19);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___lambda__2), 8, 2);
lean_closure_set(x_21, 0, x_13);
lean_closure_set(x_21, 1, x_1);
x_22 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 7, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
x_23 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_15, x_22, x_2, x_3, x_4, x_5, x_6);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = l_Lean_Expr_getAppFn(x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_9);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_10);
x_12 = lean_mk_array(x_10, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_10, x_13);
lean_dec(x_10);
lean_inc(x_2);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_12, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault), 7, 2);
lean_closure_set(x_16, 0, x_8);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_2, x_1, x_16, x_3, x_4, x_5, x_6, x_7);
return x_17;
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
x_3 = lean_unsigned_to_nat(363u);
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
x_1 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3;
x_2 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_71; uint8_t x_72; 
x_71 = lean_unsigned_to_nat(5u);
x_72 = lean_nat_dec_lt(x_71, x_5);
lean_dec(x_5);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_74 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_73);
x_12 = x_74;
goto block_70;
}
else
{
lean_object* x_75; 
x_75 = lean_array_fget(x_4, x_71);
x_12 = x_75;
goto block_70;
}
block_70:
{
lean_object* x_13; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2;
x_19 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_18, x_7, x_8, x_9, x_10, x_15);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2;
x_22 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_21, x_7, x_8, x_9, x_10, x_15);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_20, 1);
x_25 = lean_ctor_get(x_20, 0);
lean_dec(x_25);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_box(0);
lean_ctor_set(x_20, 1, x_27);
lean_ctor_set(x_20, 0, x_26);
x_28 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__4;
x_29 = l_Lean_Expr_const___override(x_28, x_20);
x_30 = l_Lean_mkApp3(x_29, x_2, x_3, x_14);
x_31 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_32 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_30, x_31, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Expr_app___override(x_6, x_33);
x_36 = lean_unsigned_to_nat(6u);
x_37 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_35, x_4, x_36, x_7, x_8, x_9, x_10, x_34);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_32);
if (x_38 == 0)
{
return x_32;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_32, 0);
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_32);
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
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2;
x_43 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_42, x_7, x_8, x_9, x_10, x_15);
return x_43;
}
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
lean_dec(x_20);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_17, 0);
lean_inc(x_45);
lean_dec(x_17);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__4;
x_49 = l_Lean_Expr_const___override(x_48, x_47);
x_50 = l_Lean_mkApp3(x_49, x_2, x_3, x_14);
x_51 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_52 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_50, x_51, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Expr_app___override(x_6, x_53);
x_56 = lean_unsigned_to_nat(6u);
x_57 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_55, x_4, x_56, x_7, x_8, x_9, x_10, x_54);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_58 = lean_ctor_get(x_52, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_60 = x_52;
} else {
 lean_dec_ref(x_52);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_44);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2;
x_63 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_62, x_7, x_8, x_9, x_10, x_15);
return x_63;
}
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1___closed__2;
x_65 = l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5(x_64, x_7, x_8, x_9, x_10, x_15);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_7);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1;
lean_inc(x_8);
x_10 = lean_mk_array(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_8, x_11);
lean_dec(x_8);
lean_inc(x_1);
x_13 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_10, x_12);
x_14 = lean_array_get_size(x_13);
x_15 = lean_nat_dec_lt(x_7, x_14);
x_16 = lean_nat_dec_lt(x_11, x_14);
x_17 = lean_unsigned_to_nat(3u);
x_18 = lean_nat_dec_lt(x_17, x_14);
if (x_15 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_39 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_38);
x_19 = x_39;
goto block_37;
}
else
{
lean_object* x_40; 
x_40 = lean_array_fget(x_13, x_7);
x_19 = x_40;
goto block_37;
}
block_37:
{
lean_object* x_20; 
if (x_16 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_35 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_34);
x_20 = x_35;
goto block_33;
}
else
{
lean_object* x_36; 
x_36 = lean_array_fget(x_13, x_11);
x_20 = x_36;
goto block_33;
}
block_33:
{
lean_object* x_21; 
lean_inc(x_13);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lambda__1), 11, 5);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_19);
lean_closure_set(x_21, 2, x_20);
lean_closure_set(x_21, 3, x_13);
lean_closure_set(x_21, 4, x_14);
if (x_18 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_13);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6;
x_23 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 7, 2);
lean_closure_set(x_25, 0, x_24);
lean_closure_set(x_25, 1, x_21);
x_26 = lean_unsigned_to_nat(6u);
x_27 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_26, x_25, x_2, x_3, x_4, x_5, x_6);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_array_fget(x_13, x_17);
lean_dec(x_13);
x_29 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg), 6, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 7, 2);
lean_closure_set(x_30, 0, x_29);
lean_closure_set(x_30, 1, x_21);
x_31 = lean_unsigned_to_nat(6u);
x_32 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_31, x_30, x_2, x_3, x_4, x_5, x_6);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__3(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__9(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__8(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwMaxRecDepthAt___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__10(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
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
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefault___spec__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toCode___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit), 6, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF___closed__1;
x_8 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___spec__1___rarg), 7, 2);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_run___rarg(x_8, x_2, x_3, x_4, x_5);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ProjFns(uint8_t builtin, lean_object*);
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
l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___lambda__1___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4 = _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__4);
l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__5 = _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__5);
l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6 = _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_seqToCode_go___closed__6);
l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_seqToCode___closed__2);
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
l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__6 = _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__6);
l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__7 = _init_l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_State_lctx___default___closed__7);
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
l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_run___rarg___closed__2);
l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__1 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__1();
l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__2 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__2();
l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__3 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__3();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__2___closed__3);
l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__1);
l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__2 = _init_l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__2);
l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__3 = _init_l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__3();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___spec__5___closed__3);
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
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__3 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___lambda__2___closed__3);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__1);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__2 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lambda__1___closed__2);
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___closed__1 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___closed__1);
l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2___closed__1 = _init_l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2___closed__1();
lean_mark_persistent(l_Lean_getProjectionFnInfo_x3f___at_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___spec__2___closed__1);
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
l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__28 = _init_l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__28();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__28);
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
